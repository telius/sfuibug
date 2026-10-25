-- ==============================================================================
--  sfuibug/sfuibug.lua
--  dedicated lightweight bug tracker and dispatcher monitor for sfui.
-- ==============================================================================

local _G = _G
local tostring, tonumber, type = _G.tostring, _G.tonumber, _G.type
local string_format, string_match, string_gsub = _G.string.format, _G.string.match, _G.string.gsub
local table_insert, table_remove = _G.table.insert, _G.table.remove
local pairs, ipairs, time = _G.pairs, _G.ipairs, _G.time
local math_min = _G.math.min
local debugstack = _G.debugstack
local InCombatLockdown = _G.InCombatLockdown
local GetBuildInfo = _G.GetBuildInfo
local CreateFrame = _G.CreateFrame
local Minimap = _G.Minimap
local GameTooltip = _G.GameTooltip

-- capture real error handlers at chunk load time before any late-loading addon can overwrite
local real_seterrorhandler = _G.seterrorhandler
local real_geterrorhandler = _G.geterrorhandler

-- global export
_G.sfuibug = _G.sfuibug or {}
local sfuibug = _G.sfuibug

-- configuration constants
local MAX_ERRORS = 25
local PREFIX = "|cff6600ffsfui|r |cffff4444[bug]|r "
-- curse of doom (spell_shadow_auraofdarkness) icon
local ICON_TEXTURE = 136122
local ICON_PATH = "Interface\\Icons\\spell_shadow_auraofdarkness"

-- throttling & burst protection constants
local BURST_WINDOW = 1.0         -- rolling rate-limit window in seconds
local BURST_MAX_NEW = 10         -- max new unique error records captured per second
local CHAT_MAX_PER_WINDOW = 3    -- max individual chat notifications per second out of combat
local MAX_FAST_CACHE = 64        -- max entries in fast raw_msg -> fp lookup cache

-- session notification throttle (fingerprint -> true)
local _notifiedThisSession = {}

-- session counters (in-memory only, strictly never written to WTF / SfuiBugDB)
local _sunkNonSfuiCount = 0
local _lastSunkMsg = nil

-- fast-path deduplication cache
local _fastFpCache = {}
local _fastFpCacheCount = 0
local _lastRawMsg = nil
local _lastFp = nil

-- burst rate limiter
local _burstWindowStart = 0
local _burstNewCount = 0
local _burstSuppressedCount = 0

-- combat and chat notification throttle
local _combatErrorsOccurred = 0
local _chatWindowStart = 0
local _chatNotifCount = 0
local _chatSuppressedCount = 0

-- badge debouncing state
local _badgeDirty = false
local _badgeTimerPending = false

-- forward declarations
local update_badge
local request_badge_update
local flush_badge
local init_minimap

-- ─── secret value safety guards ─────────────────────────────────────────────
local function is_secret_or_inaccessible(val)
    if _G.issecretvalue and _G.issecretvalue(val) then
        return true
    end
    if _G.canaccessvalue and not _G.canaccessvalue(val) then
        return true
    end
    return false
end

local function safe_string(val, fallback)
    if is_secret_or_inaccessible(val) then
        return "<secret value>"
    end
    return tostring(val or fallback or "")
end

-- ─── path and module normalizer ─────────────────────────────────────────────
local function normalize_path(path)
    if not path then return "" end
    local clean = string_gsub(path, "\\", "/")
    clean = string_gsub(clean, "^%[string \"@", "")
    clean = string_gsub(clean, "^%[string \"", "")
    clean = string_gsub(clean, "\"%]$", "")
    clean = string_gsub(clean, "^.*[Aa]dd[Oo]ns/[Ss][Ff][Uu][Ii]/", "")
    -- shorten foreign (blizzard / other addon) paths for taint reports
    clean = string_gsub(clean, "^.*[Ii]nterface/[Aa]dd[Oo]ns/", "")
    return clean
end

local function extract_module(file)
    if not file then return "core" end
    local clean = normalize_path(file)
    if string_match(clean, "^.*[Aa]dd[Oo]ns/[Ss][Ff][Uu][Ii][Bb][Uu][Gg]/") or string_match(clean, "sfuibug%.lua") then
        return "sfuibug"
    end
    local mod = string_match(clean, "^frames/([^/]+)")
        or string_match(clean, "^core/([^/]+)")
        or string_match(clean, "^data/([^/]+)")
        or string_match(clean, "^([^/%.]+)%.lua")
    return mod or "core"
end

-- ─── stack normalization ───────────────────────────────────────────────────
local function clean_stack(raw_stack)
    if not raw_stack or is_secret_or_inaccessible(raw_stack) then
        return ""
    end

    local cleaned_lines = {}
    for line in string.gmatch(raw_stack, "[^\r\n]+") do
        -- skip internal sfuibug and dispatcher wrappers
        local is_internal = string_match(line, "sfuibug")
            or string_match(line, "%[C%]: in function 'xpcall'")
            or string_match(line, "%[C%]: in function 'pcall'")
            or string_match(line, "dispatcher%.lua:[0-9]+: in function")

        if not is_internal then
            local norm_line = normalize_path(line)
            norm_line = string_gsub(norm_line, "^%s+", "")
            table_insert(cleaned_lines, norm_line)
            if #cleaned_lines >= 8 then
                break
            end
        end
    end

    return table.concat(cleaned_lines, "\n")
end

-- ─── deterministic fingerprint ──────────────────────────────────────────────
local function compute_fingerprint(mod, file, line, msg)
    local str = string_format("%s|%s|%s|%s", safe_string(mod), safe_string(file), safe_string(line), safe_string(msg))
    -- lightweight 32-bit fnv-1a hash
    local hash = 2166136261
    for i = 1, #str do
        hash = bit.bxor(hash, string.byte(str, i))
        hash = bit.band(hash * 16777619, 0xFFFFFFFF)
    end
    return string_format("%08x", hash)
end

-- ─── sfui file verification ───────────────────────────────────────────────
local SFUI_PATH_PATTERNS = {
    "[Aa]dd[Oo]ns[/\\][Ss][Ff][Uu][Ii][/\\]",
    "[Aa]dd[Oo]ns[/\\][Ss][Ff][Uu][Ii][Bb][Uu][Gg][/\\]",
}

local function path_is_sfui(path)
    if type(path) ~= "string" or is_secret_or_inaccessible(path) then
        return false
    end
    for i = 1, #SFUI_PATH_PATTERNS do
        if string_match(path, SFUI_PATH_PATTERNS[i]) then
            return true
        end
    end
    return false
end

-- ─── database initialization ───────────────────────────────────────────────
local function init_db()
    _G.SfuiBugDB = _G.SfuiBugDB or {}
    local db = _G.SfuiBugDB
    db.version = 1
    db.errors = db.errors or {}
    db.order = db.order or {}
    db.minimap = db.minimap or { hide = false }
    if db.sink == nil then
        db.sink = true -- enabled by default: universal error sink for all bugs
    end
    db.minimap.minimapPos = nil

    -- Prune any non-sfui foreign entries that may have been recorded previously (run once on load)
    if not db._pruned then
        local new_order = {}
        for _, fp in ipairs(db.order) do
            local e = db.errors[fp]
            local is_sfui = e and ((e.raw_file and path_is_sfui(e.raw_file))
                or path_is_sfui(e.file)
                or (e.module and e.module ~= "taint" and e.module ~= "unknown" and e.module ~= "blizzard"))
            if is_sfui then
                table_insert(new_order, fp)
            else
                if e then db.errors[fp] = nil end
            end
        end
        db.order = new_order
        db._pruned = true
    end

    return db
end

function sfuibug.GetSunkCount()
    return _sunkNonSfuiCount
end

function sfuibug.GetSuppressedCount()
    return _burstSuppressedCount
end

-- ─── record error API ───────────────────────────────────────────────────────
function sfuibug.RecordError(ctx, err, stack)
    local db = init_db()

    local now = time()
    local now_sec = _G.GetTime and _G.GetTime() or (time and time() or 0)
    local in_combat = InCombatLockdown and InCombatLockdown() or false
    local raw_err = safe_string(err, "unknown error")

    -- 1. Fast-path deduplication: check immediate repeat or cache
    local cached_fp = (raw_err == _lastRawMsg and _lastFp) or _fastFpCache[raw_err]
    if cached_fp then
        local entry = db.errors[cached_fp]
        if entry then
            entry.count = (entry.count or 1) + 1
            entry.last_seen = now
            if in_combat then
                entry.in_combat = true
                _combatErrorsOccurred = _combatErrorsOccurred + 1
            end
            _lastRawMsg = raw_err
            _lastFp = cached_fp
            request_badge_update()
            return cached_fp
        end
    end

    -- 2. Burst rate limiter: throttle flood of new unique errors
    if (now_sec - _burstWindowStart) >= BURST_WINDOW then
        _burstWindowStart = now_sec
        _burstNewCount = 0
    end

    if _burstNewCount >= BURST_MAX_NEW then
        _burstSuppressedCount = _burstSuppressedCount + 1
        if in_combat then
            _combatErrorsOccurred = _combatErrorsOccurred + 1
        end
        request_badge_update()
        return nil
    end
    _burstNewCount = _burstNewCount + 1

    -- 3. Extract file, line, and message (supports [string "@..."] and bare paths)
    local err_file, err_line, err_msg = string_match(raw_err, "^%[string \"@?([^%\"]+)\"%]:(%d+):%s*(.*)")
    if not err_file then
        err_file, err_line, err_msg = string_match(raw_err, "([%w_%-/\\%.@]+%.lua):(%d+):%s*(.*)")
    end
    if not err_file then
        err_msg = raw_err
        err_file = ctx and ctx.file or "unknown"
        err_line = ctx and ctx.line or 0
    end

    local is_own_file = err_file and string_match(string_gsub(err_file, "\\", "/"), "[Aa]dd[Oo]ns/[Ss][Ff][Uu][Ii]/")
    local file = normalize_path(err_file or (ctx and ctx.file))
    local line = tonumber(err_line) or (ctx and ctx.line) or 0
    local mod = (ctx and ctx.module)
        or ((err_file and not is_own_file) and "taint")
        or extract_module(file)
    local event = (ctx and ctx.event) or "none"
    local label = (ctx and ctx.label) or event

    local max_frames = in_combat and 5 or 10
    local raw_stack = safe_string(stack or (debugstack and debugstack(3, max_frames, max_frames)) or "")
    local cleaned_stk = clean_stack(raw_stack)
    local fp = compute_fingerprint(mod, file, line, err_msg)

    local build_ver, build_num, _, toc_ver = GetBuildInfo()

    if db.errors[fp] then
        -- deduplicate existing error
        local entry = db.errors[fp]
        entry.count = (entry.count or 1) + 1
        entry.last_seen = now
        entry.in_combat = in_combat or entry.in_combat
    else
        -- enforce ring buffer limit
        if #db.order >= MAX_ERRORS then
            local oldest_fp = table_remove(db.order, 1)
            if oldest_fp and db.errors[oldest_fp] then
                db.errors[oldest_fp] = nil
            end
        end

        local entry = {
            fingerprint = fp,
            module = mod,
            file = file,
            raw_file = err_file,
            line = line,
            event = label,
            message = err_msg,
            stack = cleaned_stk,
            count = 1,
            first_seen = now,
            last_seen = now,
            client_version = build_ver or "unknown",
            client_build = tonumber(build_num) or 0,
            toc_version = tonumber(toc_ver) or 0,
            in_combat = in_combat,
        }

        db.errors[fp] = entry
        table_insert(db.order, fp)
        db.total_recorded = (db.total_recorded or 0) + 1
    end

    -- update fast-path cache
    if not _fastFpCache[raw_err] then
        if _fastFpCacheCount >= MAX_FAST_CACHE then
            _fastFpCache = {}
            _fastFpCacheCount = 0
        end
        _fastFpCache[raw_err] = fp
        _fastFpCacheCount = _fastFpCacheCount + 1
    end
    _lastRawMsg = raw_err
    _lastFp = fp

    -- 4. Throttled notification (suppressed completely during combat)
    if in_combat then
        _combatErrorsOccurred = _combatErrorsOccurred + 1
    else
        if not _notifiedThisSession[fp] then
            _notifiedThisSession[fp] = true
            if (now_sec - _chatWindowStart) >= BURST_WINDOW then
                _chatWindowStart = now_sec
                _chatNotifCount = 0
            end
            if _chatNotifCount < CHAT_MAX_PER_WINDOW then
                _chatNotifCount = _chatNotifCount + 1
                local short_file = string_match(file, "([^/]+%.lua)$") or file
                local count_suffix = db.errors[fp].count > 1 and (" (x" .. db.errors[fp].count .. ")") or ""
                print(PREFIX .. "[" .. mod .. "] " .. short_file .. ":" .. line .. " - " .. err_msg .. count_suffix)
            else
                _chatSuppressedCount = _chatSuppressedCount + 1
            end
        end
    end

    request_badge_update()
    return fp
end

function sfuibug.Clear()
    local db = init_db()
    db.errors = {}
    db.order = {}
    _notifiedThisSession = {}
    _fastFpCache = {}
    _fastFpCacheCount = 0
    _lastRawMsg = nil
    _lastFp = nil
    _lastSunkMsg = nil
    _burstSuppressedCount = 0
    _combatErrorsOccurred = 0
    _chatSuppressedCount = 0
    update_badge()
    print(PREFIX .. "error database cleared.")
end

function sfuibug.GetErrors()
    local db = init_db()
    return db.errors, db.order
end

function sfuibug.List()
    local db = init_db()
    local count = #db.order
    if count == 0 then
        print(PREFIX .. "no recorded errors.")
        return
    end
    print(PREFIX .. "recorded errors (" .. count .. "):")
    for i, fp in ipairs(db.order) do
        local e = db.errors[fp]
        if e then
            print(string_format("  |cffaaaaaa#%d|r [|cff00ff88%s|r] %s:%d (x%d): %s", i, e.module, e.file, e.line, e.count, e.message))
        end
    end
end

-- ─── sfui attribution ───────────────────────────────────────────────────────
-- extract originating file from an error message
local function extract_error_file(raw_err)
    if type(raw_err) ~= "string" or is_secret_or_inaccessible(raw_err) then
        return nil
    end
    local file = string_match(raw_err, "^%[string \"@?([^%\"]+)\"%]:(%d+)")
    if not file then
        file = string_match(raw_err, "([%w_%-/\\%.@]+%.lua):(%d+)")
    end
    return file
end

local function is_sfui_related(msg, stack, addon, opts)
    -- Engine taint notices (forbidden/blocked actions) and warnings (e.g. CooldownViewer)
    -- are foreign/Blizzard notices. Sfuibug sinks them unconditionally into the void.
    if opts and (opts.taint or opts.warning) then
        return false
    end
    if type(msg) == "string" and not is_secret_or_inaccessible(msg) then
        if string_match(msg, "^%[[Ff]orbidden%]")
           or string_match(msg, "^%[[Bb]locked%]")
           or string_match(msg, "^LUA_WARNING:") then
            return false
        end
    end

    -- First priority: inspect the error location (originating file).
    local err_file = extract_error_file(msg)
    if err_file then
        return path_is_sfui(err_file)
    end

    -- If no file in message, check the stack trace for an sfui caller at the top.
    local check_stack = stack
    if not check_stack and debugstack then
        check_stack = debugstack(3, 6, 6)
    end
    if type(check_stack) == "string" and not is_secret_or_inaccessible(check_stack) then
        for line in string.gmatch(check_stack, "[^\r\n]+") do
            local stack_file = string_match(line, "([%w_%-/\\%.@]+%.lua):%d+")
            if stack_file then
                return path_is_sfui(stack_file)
            end
        end
    end

    -- If explicit addon context is provided (not taint/warning)
    if addon == "sfui" or addon == "sfuibug" then
        return true
    end

    return false
end

-- classify a captured message into a record context
local function context_for(msg, opts)
    if opts and opts.warning then
        return { module = "warning", label = "LUA_WARNING" }
    end
    if type(msg) == "string" and not is_secret_or_inaccessible(msg) then
        if string_match(msg, "^%[[Ff]orbidden%]") then
            return { module = "taint", file = "forbidden", label = "ADDON_ACTION_FORBIDDEN" }
        elseif string_match(msg, "^%[[Bb]locked%]") then
            return { module = "taint", file = "blocked", label = "ADDON_ACTION_BLOCKED" }
        end
    end
    if opts and opts.taint then
        return { module = "taint", label = "taint" }
    end
    return nil
end

-- reentrancy guard: an error inside our own capture must never loop back in
local _capturing = false

local function capture(msg, stack, opts)
    if _capturing then return end

    -- 1. Fast-path repeat check for foreign errors (avoids repeated regex/checks)
    if msg and msg == _lastSunkMsg then
        _sunkNonSfuiCount = _sunkNonSfuiCount + 1
        return
    end

    -- 2. Fast-path repeat check for known sfui errors
    if msg and msg == _lastRawMsg and _lastFp then
        local db = _G.SfuiBugDB
        if db and db.errors and db.errors[_lastFp] then
            local entry = db.errors[_lastFp]
            entry.count = (entry.count or 1) + 1
            entry.last_seen = time()
            if InCombatLockdown and InCombatLockdown() then
                entry.in_combat = true
                _combatErrorsOccurred = _combatErrorsOccurred + 1
            end
            request_badge_update()
            return
        end
    end

    if not is_sfui_related(msg, stack, opts and opts.addon, opts) then
        -- non-sfui error: sink into the void, strictly never saved to WTF / SfuiBugDB
        _sunkNonSfuiCount = _sunkNonSfuiCount + 1
        _lastSunkMsg = msg
        return
    end

    _capturing = true
    pcall(sfuibug.RecordError, context_for(msg, opts), msg, stack)
    _capturing = false
end

-- ─── blizzard error dialog suppression ─────────────────────────────────────────
-- Chaining to Blizzard's previous handler is what triggers ScriptErrorsFrame.
-- Declining to chain suppresses the popup. Blizzard frames also register
-- LUA_WARNING and blocked-action events directly, so we unregister them
-- while sink mode is active.
local GAME_EVENT_HANDLERS = {
    ADDON_ACTION_BLOCKED   = { "HandleActionBlocked", "HandleAddonActionBlocked" },
    ADDON_ACTION_FORBIDDEN = { "HandleAddonActionForbidden" },
    MACRO_ACTION_BLOCKED   = { "HandleActionBlocked", "HandleMacroActionBlocked" },
    MACRO_ACTION_FORBIDDEN = { "HandleMacroActionForbidden" },
}

local strippedGameEvents = {}

local function toggle_game_event(event, enabled)
    local GameEvent = _G.GameEvent
    if type(GameEvent) ~= "table" then return end
    if type(GameEvent.RegisterInternalEvent) ~= "function"
       or type(GameEvent.UnregisterInternalEvent) ~= "function" then return end

    local handler
    for _, name in ipairs(GAME_EVENT_HANDLERS[event]) do
        if type(GameEvent[name]) == "function" then handler = name break end
    end
    if not handler then return end

    if enabled then
        if not strippedGameEvents[event] then return end
        local ok = pcall(GameEvent.RegisterInternalEvent, event,
                         function(...) GameEvent[handler](...) end)
        if ok then strippedGameEvents[event] = nil end
    else
        if pcall(GameEvent.UnregisterInternalEvent, event) then
            strippedGameEvents[event] = true
        end
    end
end

local function set_blizzard_suppression(suppress)
    local function toggle(frame, event)
        if not (frame and frame.RegisterEvent and frame.UnregisterEvent) then return end
        if suppress then
            pcall(frame.UnregisterEvent, frame, event)
        else
            pcall(frame.RegisterEvent, frame, event)
        end
    end

    if _G.ScriptErrorsFrame then
        toggle(_G.ScriptErrorsFrame, "LUA_WARNING")
        if suppress and _G.ScriptErrorsFrame.IsShown and _G.ScriptErrorsFrame:IsShown() then
            pcall(_G.ScriptErrorsFrame.Hide, _G.ScriptErrorsFrame)
        end
    end

    for event in pairs(GAME_EVENT_HANDLERS) do
        if _G.UIParent then
            toggle(_G.UIParent, event)
        end
        toggle_game_event(event, not suppress)
    end

    if suppress and _G.StaticPopup_Hide then
        pcall(_G.StaticPopup_Hide, "ADDON_ACTION_FORBIDDEN")
        pcall(_G.StaticPopup_Hide, "ADDON_ACTION_BLOCKED")
        pcall(_G.StaticPopup_Hide, "MACRO_ACTION_FORBIDDEN")
        pcall(_G.StaticPopup_Hide, "MACRO_ACTION_BLOCKED")
    end
end

local _hookedScriptErrorsFrame = false
local function hook_script_errors_frame()
    if _hookedScriptErrorsFrame or not _G.ScriptErrorsFrame then return end
    if _G.ScriptErrorsFrame.HookScript then
        _hookedScriptErrorsFrame = true
        _G.ScriptErrorsFrame:HookScript("OnShow", function(self)
            local db = _G.SfuiBugDB
            if not db or db.sink ~= false then
                self:Hide()
            end
        end)
    end
end

-- ─── capture installation (auto-detected) ─────────────────────────────────────
-- !BugJar and BugGrabber both claim the global error handler and then replace
-- seterrorhandler with a no-op, so a plain seterrorhandler call from us is
-- silently ignored. when one of them is present we hook its record path
-- instead (which also covers blocked/forbidden/warning events they collect).
-- priority: bugjar > buggrabber > native. detect_capture() re-runs on every
-- ADDON_LOADED and at PLAYER_LOGIN, so a grabber that loads later is adopted
-- and a stolen native handler is reclaimed. hooks can't be removed, so each
-- source is installed once and only records while it is the active mode.
sfuibug.captureMode = "none"

local _bugjarHooked, _grabberHooked = false, false

local function install_bugjar()
    local bj = _G.BugJar
    if type(bj) ~= "table" or type(bj.Record) ~= "function" then return false end
    if not _bugjarHooked then
        _bugjarHooked = true
        hooksecurefunc(bj, "Record", function(_, message, stack, _, _, opts)
            if sfuibug.captureMode ~= "bugjar" then return end
            capture(message, stack, opts)
        end)
    end
    return true
end

local function install_buggrabber()
    local bg = _G.BugGrabber
    if type(bg) ~= "table" or type(bg.RegisterCallback) ~= "function" then return false end
    if not _grabberHooked then
        _grabberHooked = true
        bg.RegisterCallback(sfuibug, "BugGrabber_BugGrabbed", function(_, errObj)
            if sfuibug.captureMode ~= "buggrabber" or type(errObj) ~= "table" then return end
            capture(errObj.message, errObj.stack, nil)
        end)
    end
    return true
end

local _inErrorHandler = false
local _origErrorHandler
local function _sfuibug_global_error_handler(msg)
    if _inErrorHandler then return end
    _inErrorHandler = true

    -- a grabber may have adopted us as its "previous" handler; skip to avoid doubles
    if sfuibug.captureMode == "native" then
        capture(msg, nil, nil)
    end

    local db = _G.SfuiBugDB
    local is_sink = not db or db.sink ~= false

    _inErrorHandler = false

    -- when sink mode is disabled, forward to original handler so blizzard ui still receives it.
    -- when sink mode is enabled (default), we do NOT chain, effectively sinking the error.
    if not is_sink then
        if _origErrorHandler and _origErrorHandler ~= _sfuibug_global_error_handler then
            return pcall(_origErrorHandler, msg)
        end
    end
end

local function install_native()
    local set_eh = real_seterrorhandler or _G.seterrorhandler
    local get_eh = real_geterrorhandler or _G.geterrorhandler
    if not (set_eh and get_eh) then return false end
    local current = get_eh()
    if current == _sfuibug_global_error_handler then
        local db = _G.SfuiBugDB
        set_blizzard_suppression(not db or db.sink ~= false)
        hook_script_errors_frame()
        return true
    end
    if current and current ~= _sfuibug_global_error_handler then
        _origErrorHandler = current
    end
    pcall(set_eh, _sfuibug_global_error_handler)
    local ok = get_eh() == _sfuibug_global_error_handler
    if ok then
        local db = _G.SfuiBugDB
        set_blizzard_suppression(not db or db.sink ~= false)
        hook_script_errors_frame()
    end
    return ok
end

local _warnedNoHook = false
local function detect_capture()
    local mode = (install_bugjar() and "bugjar")
        or (install_buggrabber() and "buggrabber")
        or (install_native() and "native")
        or "none"
    sfuibug.captureMode = mode
    return mode
end
sfuibug.DetectCapture = detect_capture

-- events only needed when no grabber is collecting them for us
local function on_native_event(event, arg1, arg2)
    if sfuibug.captureMode ~= "native" then return end
    if event == "ADDON_ACTION_BLOCKED" or event == "ADDON_ACTION_FORBIDDEN" then
        if arg1 ~= "sfui" and arg1 ~= "sfuibug" then
            _sunkNonSfuiCount = _sunkNonSfuiCount + 1
            return
        end
        local label = event == "ADDON_ACTION_FORBIDDEN" and "[forbidden]" or "[blocked]"
        capture(label .. " " .. tostring(arg1) .. " tried to call the protected function '" .. safe_string(arg2) .. "'.",
            "", { addon = arg1, taint = true })
    elseif event == "MACRO_ACTION_BLOCKED" or event == "MACRO_ACTION_FORBIDDEN" then
        _sunkNonSfuiCount = _sunkNonSfuiCount + 1
    elseif event == "LUA_WARNING" then
        local text = (type(arg2) == "string" and arg2) or (type(arg1) == "string" and arg1) or nil
        if text then
            capture("LUA_WARNING: " .. text, "", { warning = true })
        end
    end
end

init_db()
detect_capture()

-- ─── minimap icon implementation ───────────────────────────────────────────
local minimapBtn = nil
local badgeText = nil
local ldbDataObject = nil

local function populate_tooltip(tt)
    if not tt then return end
    tt:AddLine("|cff6600ffsfui|r |cffff4444[bug tracker]|r")

    local db = init_db()
    local count = #db.order
    if count == 0 then
        tt:AddLine("no sfui errors captured.", 0.6, 0.9, 0.6)
    else
        tt:AddDoubleLine("sfui errors:", tostring(count), 1, 1, 1, 1, 0.28, 0.28)
        tt:AddDoubleLine("total sfui logged:", tostring(db.total_recorded or count), 1, 1, 1, 0.8, 0.8, 0.8)
        tt:AddLine(" ")
        tt:AddLine("recent sfui errors:", 1, 0.82, 0)

        local maxShow = math_min(count, 5)
        for i = 1, maxShow do
            local fp = db.order[count - i + 1]
            local e = db.errors[fp]
            if e then
                local short_file = string_match(e.file or "", "([^/]+%.lua)$") or e.file or "unknown"
                tt:AddDoubleLine(
                    string_format("  [%s] %s:%d", e.module or "core", short_file, e.line or 0),
                    string_format("x%d", e.count or 1),
                    1, 1, 1, 1, 0.5, 0.5
                )
            end
        end
    end

    if _sunkNonSfuiCount > 0 then
        tt:AddLine(" ")
        tt:AddDoubleLine("other bugs sunk:", tostring(_sunkNonSfuiCount), 0.7, 0.7, 0.7, 0.4, 0.9, 0.4)
    end
    if _burstSuppressedCount > 0 then
        tt:AddDoubleLine("flood throttled:", tostring(_burstSuppressedCount), 1, 0.7, 0.3, 1, 0.7, 0.3)
    end

    tt:AddLine(" ")
    tt:AddLine("|cff00ff88left-click|r: print error list in chat", 0.8, 0.8, 0.8)
    tt:AddLine("|cff00ff88right-click|r: clear error database", 0.8, 0.8, 0.8)
end

flush_badge = function()
    _badgeTimerPending = false
    _badgeDirty = false

    local db = init_db()
    local count = #db.order
    local text = count > 0 and tostring(count) or ""

    if badgeText then
        badgeText:SetText(text)
        if count > 0 then
            badgeText:Show()
        else
            badgeText:Hide()
        end
    end

    if ldbDataObject then
        ldbDataObject.text = tostring(count)
    end

    if _chatSuppressedCount > 0 and not (InCombatLockdown and InCombatLockdown()) then
        print(PREFIX .. "... and " .. _chatSuppressedCount .. " additional error(s). type |cff00ff88/sfuibug list|r to inspect.")
        _chatSuppressedCount = 0
    end
end

request_badge_update = function()
    _badgeDirty = true
    if InCombatLockdown and InCombatLockdown() then
        return
    end
    if _badgeTimerPending then
        return
    end
    _badgeTimerPending = true
    if _G.C_Timer and _G.C_Timer.After then
        _G.C_Timer.After(0.2, flush_badge)
    else
        flush_badge()
    end
end

update_badge = function()
    flush_badge()
end

init_minimap = function()
    local db = init_db()

    -- 1. Try LibDataBroker + LibDBIcon integration (standard across sfui & broker bars)
    local ldb = _G.LibStub and _G.LibStub("LibDataBroker-1.1", true)
    local ldbi = _G.LibStub and _G.LibStub("LibDBIcon-1.0", true)

    if ldb and ldbi then
        if not ldbDataObject then
            ldbDataObject = ldb:NewDataObject("sfuibug", {
                type = "data source",
                text = "0",
                icon = ICON_TEXTURE,
                OnClick = function(_, button)
                    if button == "RightButton" then
                        sfuibug.Clear()
                    else
                        sfuibug.List()
                    end
                end,
                OnTooltipShow = function(tt)
                    populate_tooltip(tt)
                end,
                OnLeave = function()
                    if GameTooltip and GameTooltip:IsShown() then
                        GameTooltip:Hide()
                    end
                end,
            })

            ldbi:Register("sfuibug", ldbDataObject, db.minimap)
        end

        local iconBtn = ldbi:GetMinimapButton("sfuibug")
        if iconBtn then
            minimapBtn = iconBtn
            iconBtn:HookScript("OnLeave", function()
                if GameTooltip and GameTooltip:IsShown() then
                    GameTooltip:Hide()
                end
            end)
            if iconBtn.icon then
                iconBtn.icon:SetTexture(ICON_TEXTURE)
                iconBtn.icon:SetTexCoord(0.08, 0.92, 0.08, 0.92)
            end
            if not badgeText then
                badgeText = iconBtn:CreateFontString(nil, "OVERLAY", "NumberFontNormalSmall")
                badgeText:SetPoint("BOTTOMRIGHT", iconBtn, "BOTTOMRIGHT", 2, 0)
                badgeText:SetTextColor(1, 0.28, 0.28, 1)
            end
            update_badge()
            return
        end
    end

    -- 2. Native dependency-free minimap button fallback
    if not minimapBtn and Minimap then
        local btn = CreateFrame("Button", "SfuiBugMinimapButton", Minimap)
        btn:SetSize(31, 31)
        btn:SetFrameStrata("MEDIUM")
        btn:SetFrameLevel(8)
        btn:EnableMouse(true)
        btn:RegisterForClicks("LeftButtonUp", "RightButtonUp")

        -- icon texture (curse of doom)
        local icon = btn:CreateTexture(nil, "BACKGROUND")
        icon:SetSize(20, 20)
        icon:SetPoint("CENTER", btn, "CENTER", 0, 0)
        icon:SetTexture(ICON_TEXTURE)
        icon:SetTexCoord(0.08, 0.92, 0.08, 0.92)
        btn.icon = icon

        -- circular minimap border
        local border = btn:CreateTexture(nil, "OVERLAY")
        border:SetSize(52, 52)
        border:SetPoint("TOPLEFT", btn, "TOPLEFT", -1, 1)
        border:SetTexture("Interface\\Minimap\\MiniMap-TrackingBorder")

        -- highlight
        local highlight = btn:CreateTexture(nil, "HIGHLIGHT")
        highlight:SetSize(20, 20)
        highlight:SetPoint("CENTER", btn, "CENTER", 0, 0)
        highlight:SetTexture("Interface\\Minimap\\UI-Minimap-ZoomButton-Highlight")

        -- error counter badge
        badgeText = btn:CreateFontString(nil, "OVERLAY", "NumberFontNormalSmall")
        badgeText:SetPoint("BOTTOMRIGHT", btn, "BOTTOMRIGHT", 2, 0)
        badgeText:SetTextColor(1, 0.28, 0.28, 1)

        -- scripts
        btn:SetScript("OnClick", function(_, button)
            if button == "RightButton" then
                sfuibug.Clear()
            else
                sfuibug.List()
            end
        end)

        local function show_native_tooltip(owner)
            if not owner or not GameTooltip then return end
            GameTooltip:SetOwner(owner, "ANCHOR_BOTTOMLEFT")
            GameTooltip:ClearLines()
            populate_tooltip(GameTooltip)
            GameTooltip:Show()
        end

        btn:SetScript("OnEnter", function(self)
            show_native_tooltip(self)
        end)

        btn:SetScript("OnLeave", function(self)
            if GameTooltip and GameTooltip:GetOwner() == self then
                GameTooltip:Hide()
            end
        end)

        btn:SetPoint("CENTER", Minimap, "CENTER", 0, 0)
        minimapBtn = btn

        if db.minimap.hide then
            btn:Hide()
        else
            btn:Show()
        end
    end

    update_badge()
end

function sfuibug.ToggleMinimap()
    local db = init_db()
    db.minimap.hide = not db.minimap.hide

    local ldbi = _G.LibStub and _G.LibStub("LibDBIcon-1.0", true)
    if ldbi and ldbi:GetMinimapButton("sfuibug") then
        if db.minimap.hide then
            ldbi:Hide("sfuibug")
        else
            ldbi:Show("sfuibug")
        end
    elseif minimapBtn then
        if db.minimap.hide then
            minimapBtn:Hide()
        else
            minimapBtn:Show()
        end
    end

    print(PREFIX .. "minimap icon " .. (db.minimap.hide and "hidden" or "shown") .. ".")
end

-- ─── slash command handler ─────────────────────────────────────────────────
local function slash_cmd(msg)
    local cmd = string.lower(string_match(msg or "", "^%s*(%S+)") or "")
    local db = init_db()

    if cmd == "clear" or cmd == "wipe" then
        sfuibug.Clear()
    elseif cmd == "list" or cmd == "show" then
        sfuibug.List()
    elseif cmd == "icon" or cmd == "minimap" then
        sfuibug.ToggleMinimap()
    elseif cmd == "sink" then
        db.sink = not db.sink
        set_blizzard_suppression(db.sink)
        print(PREFIX .. "universal error sink " .. (db.sink and "|cff00ff88enabled|r (all errors sunk, only sfui logged)" or "|cffff4444disabled|r (blizzard popups active)") .. ".")
    else
        local count = #db.order
        print(PREFIX .. "sfui errors: " .. count .. " (total logged: " .. (db.total_recorded or 0) .. ")")
        if _sunkNonSfuiCount > 0 then
            print("  other bugs sunk: |cff00ff88" .. _sunkNonSfuiCount .. "|r (swallowed without logging)")
        end
        if _burstSuppressedCount > 0 then
            print("  flood throttled: |cffffaa00" .. _burstSuppressedCount .. "|r (burst errors suppressed)")
        end
        print("  capture mode: |cff00ff88" .. detect_capture() .. "|r (auto-detected)")
        print("  universal sink: " .. (db.sink ~= false and "|cff00ff88enabled|r" or "|cffff4444disabled|r"))
        print("  |cff00ff88/sfuibug list|r to inspect errors.")
        print("  |cff00ff88/sfuibug clear|r to reset database.")
        print("  |cff00ff88/sfuibug sink|r to toggle universal error sink.")
        print("  |cff00ff88/sfuibug icon|r to toggle minimap button.")
    end
end

_G.SLASH_SFUIBUG1 = "/sfuibug"
_G.SLASH_SFUIBUG2 = "/sfbug"
_G.SlashCmdList["SFUIBUG"] = slash_cmd

-- ─── frame initialization ───────────────────────────────────────────────────
local f = CreateFrame("Frame")
f:RegisterEvent("ADDON_LOADED")
f:RegisterEvent("PLAYER_LOGIN")
f:RegisterEvent("PLAYER_REGEN_DISABLED")
f:RegisterEvent("PLAYER_REGEN_ENABLED")
-- always registered; on_native_event ignores them unless mode is native
f:RegisterEvent("ADDON_ACTION_BLOCKED")
f:RegisterEvent("ADDON_ACTION_FORBIDDEN")
f:RegisterEvent("MACRO_ACTION_BLOCKED")
f:RegisterEvent("MACRO_ACTION_FORBIDDEN")
f:RegisterEvent("LUA_WARNING")
f:SetScript("OnEvent", function(_, event, arg1, arg2)
    if event == "ADDON_LOADED" then
        if arg1 == "sfuibug" then
            init_db()
            local db = _G.SfuiBugDB
            if db and db.sink ~= false then
                set_blizzard_suppression(true)
                hook_script_errors_frame()
            end
        elseif arg1 == "Blizzard_ScriptErrorsFrame" then
            local db = _G.SfuiBugDB
            if db and db.sink ~= false then
                set_blizzard_suppression(true)
                hook_script_errors_frame()
            end
        end
        -- a grabber (or handler thief) may have just loaded
        detect_capture()
    elseif event == "PLAYER_LOGIN" then
        init_db()
        detect_capture()
        local db = _G.SfuiBugDB
        if db and db.sink ~= false then
            set_blizzard_suppression(true)
            hook_script_errors_frame()
        end
        if detect_capture() == "none" and not _warnedNoHook then
            _warnedNoHook = true
            print(PREFIX .. "warning: could not install an error hook, errors will not be captured.")
        end
        init_minimap()
    elseif event == "PLAYER_REGEN_DISABLED" then
        -- combat start
    elseif event == "PLAYER_REGEN_ENABLED" then
        -- combat end: flush any deferred badge and combat notices
        if _badgeDirty then
            flush_badge()
        end
        if _combatErrorsOccurred > 0 then
            print(PREFIX .. _combatErrorsOccurred .. " sfui error(s) occurred during combat. type |cff00ff88/sfuibug list|r to inspect.")
            _combatErrorsOccurred = 0
        end
        if _burstSuppressedCount > 0 then
            print(PREFIX .. _burstSuppressedCount .. " burst error(s) were throttled to prevent gameplay lag.")
            _burstSuppressedCount = 0
        end
    else
        on_native_event(event, arg1, arg2)
    end
end)

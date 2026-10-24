-- ==============================================================================
--  sfuibug/sfuibug.lua
--  dedicated lightweight bug tracker and dispatcher monitor for sfui.
-- ==============================================================================

local _G = _G
local tostring, tonumber, type = _G.tostring, _G.tonumber, _G.type
local string_format, string_match, string_gsub = _G.string.format, _G.string.match, _G.string.gsub
local table_insert, table_remove = _G.table.insert, _G.table.remove
local pairs, ipairs, time = _G.pairs, _G.ipairs, _G.time
local debugstack = _G.debugstack
local InCombatLockdown = _G.InCombatLockdown
local GetBuildInfo = _G.GetBuildInfo

-- global export
_G.sfuibug = _G.sfuibug or {}
local sfuibug = _G.sfuibug

-- configuration constants
local MAX_ERRORS = 25
local PREFIX = "|cff6600ffsfui|r |cffff4444[bug]|r "

-- session notification throttle (fingerprint -> true)
local _notifiedThisSession = {}

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
    return clean
end

local function extract_module(file)
    if not file then return "core" end
    local clean = normalize_path(file)
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

-- ─── database initialization ───────────────────────────────────────────────
local function init_db()
    _G.SfuiBugDB = _G.SfuiBugDB or {}
    local db = _G.SfuiBugDB
    db.version = 1
    db.errors = db.errors or {}
    db.order = db.order or {}
    db.total_recorded = db.total_recorded or 0
    return db
end

-- ─── record error API ───────────────────────────────────────────────────────
function sfuibug.RecordError(ctx, err, stack)
    local db = init_db()

    local raw_err = safe_string(err, "unknown error")
    local raw_stack = safe_string(stack or debugstack(2, 10, 10))

    -- extract file, line, and message
    local err_file, err_line, err_msg = string_match(raw_err, "([%w_%-/\\%.]+%.lua):(%d+):%s*(.*)")
    if not err_file then
        err_msg = raw_err
        err_file = ctx and ctx.file or "unknown"
        err_line = ctx and ctx.line or 0
    end

    local file = normalize_path(err_file or (ctx and ctx.file))
    local line = tonumber(err_line) or (ctx and ctx.line) or 0
    local mod = (ctx and ctx.module) or extract_module(file)
    local event = (ctx and ctx.event) or "none"
    local label = (ctx and ctx.label) or event

    local cleaned_stk = clean_stack(raw_stack)
    local fp = compute_fingerprint(mod, file, line, err_msg)

    local now = time()
    local in_combat = InCombatLockdown and InCombatLockdown() or false
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

    -- print throttled user notification in chat
    if not _notifiedThisSession[fp] then
        _notifiedThisSession[fp] = true
        local short_file = string_match(file, "([^/]+%.lua)$") or file
        local count_suffix = db.errors[fp].count > 1 and (" (x" .. db.errors[fp].count .. ")") or ""
        print(PREFIX .. "[" .. mod .. "] " .. short_file .. ":" .. line .. " - " .. err_msg .. count_suffix)
    end

    return fp
end

function sfuibug.Clear()
    local db = init_db()
    db.errors = {}
    db.order = {}
    _notifiedThisSession = {}
    print(PREFIX .. "error database cleared.")
end

function sfuibug.GetErrors()
    local db = init_db()
    return db.errors, db.order
end

-- ─── global error handler hook ─────────────────────────────────────────────
local _origErrorHandler = _G.geterrorhandler and _G.geterrorhandler()

local function _sfuibug_global_error_handler(msg)
    local raw_stack = debugstack(2, 12, 12)
    -- check if sfui is in the stack trace
    if string_match(raw_stack, "[Aa]dd[Oo]ns/[Ss][Ff][Uu][Ii]") then
        sfuibug.RecordError(nil, msg, raw_stack)
    end

    -- forward to original handler so external tools or blizzard UI receive it
    if _origErrorHandler and _origErrorHandler ~= _sfuibug_global_error_handler then
        return _origErrorHandler(msg)
    end
end

if _G.seterrorhandler then
    _G.seterrorhandler(_sfuibug_global_error_handler)
end

-- ─── slash command handler ─────────────────────────────────────────────────
local function slash_cmd(msg)
    local cmd = string.lower(string_match(msg or "", "^%s*(%S+)") or "")
    local db = init_db()

    if cmd == "clear" or cmd == "wipe" then
        sfuibug.Clear()
    elseif cmd == "list" or cmd == "show" then
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
    else
        local count = #db.order
        print(PREFIX .. "active errors: " .. count .. " (total logged: " .. (db.total_recorded or 0) .. ")")
        print("  type |cff00ff88/sfuibug list|r to inspect or |cff00ff88/sfuibug clear|r to reset.")
    end
end

_G.SLASH_SFUIBUG1 = "/sfuibug"
_G.SLASH_SFUIBUG2 = "/sfbug"
_G.SlashCmdList["SFUIBUG"] = slash_cmd

-- ─── frame initialization ───────────────────────────────────────────────────
local f = _G.CreateFrame("Frame")
f:RegisterEvent("ADDON_LOADED")
f:SetScript("OnEvent", function(_, event, name)
    if name == "sfuibug" then
        init_db()
    end
end)

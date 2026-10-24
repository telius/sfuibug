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

-- global export
_G.sfuibug = _G.sfuibug or {}
local sfuibug = _G.sfuibug

-- configuration constants
local MAX_ERRORS = 25
local PREFIX = "|cff6600ffsfui|r |cffff4444[bug]|r "
-- curse of doom (spell_shadow_auraofdarkness) icon
local ICON_TEXTURE = 136122
local ICON_PATH = "Interface\\Icons\\spell_shadow_auraofdarkness"

-- session notification throttle (fingerprint -> true)
local _notifiedThisSession = {}

-- forward declarations
local update_badge
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
    db.minimap = db.minimap or { hide = false }
    db.minimap.minimapPos = nil
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

    update_badge()
    return fp
end

function sfuibug.Clear()
    local db = init_db()
    db.errors = {}
    db.order = {}
    _notifiedThisSession = {}
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
        tt:AddLine("no errors captured.", 0.6, 0.9, 0.6)
    else
        tt:AddDoubleLine("active errors:", tostring(count), 1, 1, 1, 1, 0.28, 0.28)
        tt:AddDoubleLine("total logged:", tostring(db.total_recorded or count), 1, 1, 1, 0.8, 0.8, 0.8)
        tt:AddLine(" ")
        tt:AddLine("recent errors:", 1, 0.82, 0)

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

    tt:AddLine(" ")
    tt:AddLine("|cff00ff88left-click|r: print error list in chat", 0.8, 0.8, 0.8)
    tt:AddLine("|cff00ff88right-click|r: clear error database", 0.8, 0.8, 0.8)
end

update_badge = function()
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
    else
        local count = #db.order
        print(PREFIX .. "active errors: " .. count .. " (total logged: " .. (db.total_recorded or 0) .. ")")
        print("  |cff00ff88/sfuibug list|r to inspect errors.")
        print("  |cff00ff88/sfuibug clear|r to reset database.")
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
f:SetScript("OnEvent", function(_, event, name)
    if event == "ADDON_LOADED" and name == "sfuibug" then
        init_db()
    elseif event == "PLAYER_LOGIN" then
        init_minimap()
    end
end)

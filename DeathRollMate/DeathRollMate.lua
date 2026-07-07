--[[
DeathRollMate
A compact Death Roll helper addon for World of Warcraft 3.3.5a / WotLK.

Implemented rules and features:
- Manual UI only: the panel is shown with /dr or /deathroll.
- The first valid roll arms/starts the game after New Game.
- The next expected max is always the previous valid roll.
- Valid rollers auto-join when they match scope/range rules; addon join requests are optional host-approved entry requests.
- Optional strict range validation.
- Optional per-turn timeout with DBM-style countdown popup.
- Countdown does not start on invite acceptance; it starts only after the first valid roll.
- Timed-out player is eliminated and treated as a loser.
- Optional bet tracking in gold/silver/copper.
- Report target can be auto/say/party/raid/me.
- Watch scope controls which manual /roll system messages are accepted: visible/party/raid/nearby.
- Invite scope is explicit and simple: target/party/raid. Only players with the addon receive popup invites.
- Players without the addon can still join by making a valid manual /roll, which is detected from CHAT_MSG_SYSTEM.
- Addon communication synchronizes offers, join requests, turn updates and results.
- Invite is sent via addon communication only; normal chat announcements remain separate.
- Incoming addon invites show a confirmation popup with bet/rule/scope details; remote timers start only after the player accepts/joins.
- Game and config UI use a compact dark ElvUI-inspired visual style.
- 1.6 adds game presets, host-authoritative roll sync, rejection reasons, settlement tracking, version checks, sounds, session restore, minimap button, admin and test commands.

Important WotLK limitation:
- /roll results arrive as CHAT_MSG_SYSTEM. There is no reliable original say/party/raid channel metadata.
- 30-yard filtering is only reliable for known party/raid unit tokens and is used only for optional roll watch filtering, not for invite broadcast.
]]

local ADDON_NAME = "DeathRollMate"
local VERSION = "1.6.3"
local COMM_PREFIX = "DRMATE"
local MINIMAP_ICON = "Interface\\AddOns\\DeathRollMate\\Media\\DiceMinimap"
local MINIMAP_FALLBACK_ICON = "Interface\\Icons\\INV_Misc_Dice_01"

local DR = CreateFrame("Frame")
_G.DeathRollMate = DR

local DEFAULTS = {
    startRoll = 1000,
    minRoll = 1,
    oneMeans = "WIN", -- WIN or LOSE
    gameMode = "REVERSE", -- CLASSIC, REVERSE, ELIMINATION, FREE
    betMode = "POT", -- POT, WINNER_TAKES, LOSER_PAYS
    autoJoin = true,
    validateRange = true,
    lockParticipants = false,
    lockFrame = false,
    reportChannel = "AUTO", -- AUTO, SAY, PARTY, RAID, SELF
    watchScope = "SAY", -- SAY=all visible roll system messages, PARTY, RAID, NEARBY
    inviteScope = "PARTY", -- who receives addon invites: TARGET, PARTY, RAID
    joinScope = "SAY", -- legacy/deprecated; valid manual rolls are governed by watch scope and range validation
    requireJoinRequest = true,
    autoReportResult = true,
    timeoutEnabled = true,
    timeoutSeconds = 10,
    showCountdown = true,
    soundEnabled = true,
    minimapEnabled = true,
    betGold = 0,
    betSilver = 0,
    betCopper = 0,
    commEnabled = true,
    acceptRemoteSync = true,
    scale = 1.0,
    point = "CENTER",
    relativePoint = "CENTER",
    x = 0,
    y = 0,
    visible = false,
    countdownPoint = "CENTER",
    countdownRelativePoint = "CENTER",
    countdownX = 0,
    countdownY = 170,
}

local REPORT_CHANNELS = { "AUTO", "SAY", "PARTY", "RAID", "SELF" }
local WATCH_SCOPES = { "SAY", "PARTY", "RAID", "NEARBY" }
local INVITE_SCOPES = { "TARGET", "PARTY", "RAID" }
local GAME_MODES = { "REVERSE", "CLASSIC", "ELIMINATION", "FREE" }
local BET_MODES = { "POT", "WINNER_TAKES", "LOSER_PAYS" }

local state = "IDLE" -- IDLE, ARMED, ACTIVE, DONE
local currentMax = nil
local lastPlayer = nil
local lastRoll = nil
local lastRange = nil
local warningText = nil
local resultText = nil
local nextPlayer = nil
local hostName = nil
local remoteHost = nil
local gameId = nil
local pendingOffer = nil
local pendingJoinRequest = nil

local participants = {}
local participantOrder = {}
local history = {}
local settlementEntries = {}
local auditLog = {}
local versionPeers = {}
local ui = {}
local countdown = {}
local settlementUi = {}

local timeoutDeadline = nil
local timeoutStartTime = nil
local timeoutTarget = nil
local timeoutKind = nil
local timeoutUiAccumulator = 0
local countdownLastSecond = nil
local sessionRestorePromptShown = false

local RefreshUI
local NormalizeName
local BuildScopeLabel
local ShowSettlementPanel
local SaveSessionSnapshot
local SendRollAcceptedComm
local SendRejectComm
local SendPlayerJoinedComm
local BuildGameModeLabel
local BuildBetModeLabel
local UpdateMinimapButton
local ToggleConfig
local StopTimeout

local function CopyDefaults(target, defaults)
    if type(target) ~= "table" then
        target = {}
    end

    for key, value in pairs(defaults) do
        if target[key] == nil then
            if type(value) == "table" then
                target[key] = CopyDefaults({}, value)
            else
                target[key] = value
            end
        end
    end

    return target
end

local function NormalizeMoney()
    local db = DeathRollMateDB
    db.betGold = math.max(0, math.floor(tonumber(db.betGold) or 0))
    db.betSilver = math.max(0, math.floor(tonumber(db.betSilver) or 0))
    db.betCopper = math.max(0, math.floor(tonumber(db.betCopper) or 0))

    if db.betCopper > 99 then
        db.betSilver = db.betSilver + math.floor(db.betCopper / 100)
        db.betCopper = db.betCopper % 100
    end
    if db.betSilver > 99 then
        db.betGold = db.betGold + math.floor(db.betSilver / 100)
        db.betSilver = db.betSilver % 100
    end
end

local function DB()
    DeathRollMateDB = CopyDefaults(DeathRollMateDB, DEFAULTS)

    -- 1.4.4 changed this setting from "rolls require prior request" to
    -- "addon join requests need host approval". Enable the safer host-approval
    -- default once for existing saved variables.
    if not DeathRollMateDB.joinApprovalMigrated144 then
        DeathRollMateDB.requireJoinRequest = true
        DeathRollMateDB.joinApprovalMigrated144 = true
    end

    if DeathRollMateDB.watchScope == "ME" then DeathRollMateDB.watchScope = "SAY" end
    if DeathRollMateDB.watchScope ~= "SAY" and DeathRollMateDB.watchScope ~= "PARTY" and DeathRollMateDB.watchScope ~= "RAID" and DeathRollMateDB.watchScope ~= "NEARBY" then
        DeathRollMateDB.watchScope = "SAY"
    end
    -- 1.5.3 split addon invite delivery from manual roll eligibility.
    -- Existing joinScope values are kept for backward compatibility but no longer
    -- block valid manual /roll based entry.
    if DeathRollMateDB.inviteScope == nil then
        if DeathRollMateDB.joinScope == "RAID" then
            DeathRollMateDB.inviteScope = "RAID"
        elseif DeathRollMateDB.joinScope == "PARTY" then
            DeathRollMateDB.inviteScope = "PARTY"
        else
            DeathRollMateDB.inviteScope = "PARTY"
        end
    end
    if DeathRollMateDB.inviteScope ~= "TARGET" and DeathRollMateDB.inviteScope ~= "PARTY" and DeathRollMateDB.inviteScope ~= "RAID" then
        DeathRollMateDB.inviteScope = "PARTY"
    end
    DeathRollMateDB.joinScope = "SAY"

    if DeathRollMateDB.gameMode ~= "CLASSIC" and DeathRollMateDB.gameMode ~= "REVERSE" and DeathRollMateDB.gameMode ~= "ELIMINATION" and DeathRollMateDB.gameMode ~= "FREE" then
        DeathRollMateDB.gameMode = "REVERSE"
    end
    if DeathRollMateDB.betMode ~= "POT" and DeathRollMateDB.betMode ~= "WINNER_TAKES" and DeathRollMateDB.betMode ~= "LOSER_PAYS" then
        DeathRollMateDB.betMode = "POT"
    end

    local seconds = tonumber(DeathRollMateDB.timeoutSeconds) or DEFAULTS.timeoutSeconds
    if seconds < 0 then seconds = DEFAULTS.timeoutSeconds end
    DeathRollMateDB.timeoutSeconds = math.floor(seconds)

    DeathRollMateDB.startRoll = math.max(2, math.floor(tonumber(DeathRollMateDB.startRoll) or DEFAULTS.startRoll))
    DeathRollMateDB.minRoll = math.max(1, math.floor(tonumber(DeathRollMateDB.minRoll) or DEFAULTS.minRoll))
    if DeathRollMateDB.minRoll >= DeathRollMateDB.startRoll then
        DeathRollMateDB.minRoll = DEFAULTS.minRoll
    end

    NormalizeMoney()
    return DeathRollMateDB
end

local function Print(message)
    DEFAULT_CHAT_FRAME:AddMessage("|cffd6b35aDeathRollMate:|r " .. tostring(message))
end

local function SetWarning(message)
    warningText = message
    if message and message ~= "" then
        Print(message)
    end
end

local function ClearTable(tbl)
    for key in pairs(tbl) do
        tbl[key] = nil
    end
end

local function CopyTableShallow(source)
    local result = {}
    if type(source) ~= "table" then return result end
    for key, value in pairs(source) do
        if type(value) == "table" then
            local child = {}
            for ck, cv in pairs(value) do child[ck] = cv end
            result[key] = child
        else
            result[key] = value
        end
    end
    return result
end

local function Audit(message)
    local stamp = date and date("%H:%M:%S") or tostring(math.floor(GetTime() or 0))
    table.insert(auditLog, "[" .. stamp .. "] " .. tostring(message or ""))
    while #auditLog > 120 do table.remove(auditLog, 1) end
end

local function PlayFeedbackSound(kind)
    if not DB().soundEnabled then return end
    if not PlaySound then return end
    local soundName = "igMainMenuOptionCheckBoxOn"
    if kind == "warn" then
        soundName = "RaidWarning"
    elseif kind == "timeout" then
        soundName = "igQuestFailed"
    elseif kind == "result" then
        soundName = "LEVELUPSOUND"
    end
    pcall(PlaySound, soundName)
end

NormalizeName = function(name)
    if not name then return nil end
    return string.match(tostring(name), "^([^%-]+)") or tostring(name)
end

local function OwnName()
    return UnitName("player") or "player"
end

local function IsCurrentPlayer(player)
    return NormalizeName(player) == NormalizeName(OwnName())
end

local function IsLocalHost()
    return hostName and NormalizeName(hostName) == NormalizeName(OwnName())
end

local function HasRemoteHost()
    return remoteHost and NormalizeName(remoteHost) ~= NormalizeName(OwnName())
end

local function IsJoinAccepted(player)
    player = NormalizeName(player)
    if not player or not participants[player] then return false end
    return participants[player].accepted == true
end

local function CountParticipants()
    return #participantOrder
end

local function IsParticipantActive(player)
    return participants[player] and not participants[player].eliminated
end

local function CountActiveParticipants()
    local count = 0
    for i = 1, #participantOrder do
        if IsParticipantActive(participantOrder[i]) then
            count = count + 1
        end
    end
    return count
end

local function GetActiveParticipantNames(exceptPlayer)
    local result = {}
    local except = NormalizeName(exceptPlayer)
    for i = 1, #participantOrder do
        local name = participantOrder[i]
        if IsParticipantActive(name) and (not except or NormalizeName(name) ~= except) then
            table.insert(result, name)
        end
    end
    return result
end

local function JoinNames(names)
    if not names or #names == 0 then return "none" end
    local text = ""
    for i = 1, #names do
        if i > 1 then text = text .. ", " end
        text = text .. names[i]
    end
    return text
end

local function FindNextActivePlayerAfter(player)
    local count = #participantOrder
    if count == 0 then return nil end

    local startIndex = 1
    local target = NormalizeName(player)
    if target then
        for i = 1, count do
            if NormalizeName(participantOrder[i]) == target then
                startIndex = i + 1
                break
            end
        end
    end

    for offset = 0, count - 1 do
        local index = ((startIndex - 1 + offset) % count) + 1
        local candidate = participantOrder[index]
        if IsParticipantActive(candidate) then
            return candidate
        end
    end

    return nil
end

local function GetNumRaidMembersSafe()
    if GetNumRaidMembers then return GetNumRaidMembers() or 0 end
    return 0
end

local function GetNumPartyMembersSafe()
    if GetNumPartyMembers then return GetNumPartyMembers() or 0 end
    return 0
end

local function GetUnitTokenForPlayer(player)
    local target = NormalizeName(player)
    if not target then return nil end

    if IsCurrentPlayer(target) then return "player" end

    if UnitExists and UnitIsPlayer and UnitName then
        if UnitExists("target") and UnitIsPlayer("target") and NormalizeName(UnitName("target")) == target then
            return "target"
        end
        if UnitExists("mouseover") and UnitIsPlayer("mouseover") and NormalizeName(UnitName("mouseover")) == target then
            return "mouseover"
        end
    end

    for i = 1, GetNumPartyMembersSafe() do
        local token = "party" .. tostring(i)
        if UnitExists(token) and NormalizeName(UnitName(token)) == target then
            return token
        end
    end

    for i = 1, GetNumRaidMembersSafe() do
        local token = "raid" .. tostring(i)
        if UnitExists(token) and NormalizeName(UnitName(token)) == target then
            return token
        end
    end

    return nil
end

local function GetRaidSubgroup(player)
    if not GetRaidRosterInfo then return nil end
    local target = NormalizeName(player)
    if not target then return nil end

    for i = 1, GetNumRaidMembersSafe() do
        local name, _, subgroup = GetRaidRosterInfo(i)
        if NormalizeName(name) == target then
            return subgroup
        end
    end

    return nil
end

local function IsInParty(player)
    local target = NormalizeName(player)
    if not target then return false end
    if IsCurrentPlayer(player) then return true end

    if GetNumRaidMembersSafe() > 0 then
        local ownSubgroup = GetRaidSubgroup(OwnName())
        local targetSubgroup = GetRaidSubgroup(player)
        return ownSubgroup ~= nil and ownSubgroup == targetSubgroup
    end

    for i = 1, GetNumPartyMembersSafe() do
        if NormalizeName(UnitName("party" .. tostring(i))) == target then
            return true
        end
    end

    return false
end

local function IsInRaid(player)
    local target = NormalizeName(player)
    if not target then return false end
    if IsCurrentPlayer(player) then return true end

    for i = 1, GetNumRaidMembersSafe() do
        if NormalizeName(UnitName("raid" .. tostring(i))) == target then
            return true
        end
    end

    return false
end

local function IsNearby(player)
    if IsCurrentPlayer(player) then return true end

    local token = GetUnitTokenForPlayer(player)
    if not token then return false end

    -- CheckInteractDistance index 4 is commonly used as the follow/interact range check, roughly near 28-30 yards.
    if CheckInteractDistance and CheckInteractDistance(token, 4) then
        return true
    end

    if UnitInRange then
        local inRange = UnitInRange(token)
        if inRange == 1 or inRange == true then
            return true
        end
    end

    return false
end

local function IsInScope(player, scope)
    scope = scope or "SAY"
    if scope == "PARTY" then return IsInParty(player) end
    if scope == "RAID" then return IsInRaid(player) end
    if scope == "NEARBY" then return IsNearby(player) end
    return true
end

local function IsRollInWatchScope(player)
    return IsInScope(player, DB().watchScope or "SAY")
end

local function IsJoinEligible(player)
    -- Valid manual /roll entry is intentionally not gated by invite scope.
    -- Eligibility for manual entry is already enforced by watch scope and range validation.
    return true
end

local function GetBetCopperValue()
    local db = DB()
    return ((tonumber(db.betGold) or 0) * 10000) + ((tonumber(db.betSilver) or 0) * 100) + (tonumber(db.betCopper) or 0)
end

local function FormatMoney(copper)
    copper = math.max(0, math.floor(tonumber(copper) or 0))
    local gold = math.floor(copper / 10000)
    copper = copper - (gold * 10000)
    local silver = math.floor(copper / 100)
    copper = copper - (silver * 100)

    if gold > 0 then return gold .. "g " .. silver .. "s " .. copper .. "c" end
    if silver > 0 then return silver .. "s " .. copper .. "c" end
    return copper .. "c"
end

local function BuildBetLabel()
    local copper = GetBetCopperValue()
    if copper <= 0 then return "Bet: off" end
    local mode = DB().betMode or "POT"
    local modeText = mode == "LOSER_PAYS" and "loser pays" or (mode == "WINNER_TAKES" and "winner takes" or "pot")
    return "Bet: " .. FormatMoney(copper) .. " / player (" .. modeText .. ")"
end

local function BuildOfferRuleLabel(oneMeans)
    if oneMeans == "LOSE" then return "minimum roll loses" end
    return "minimum roll wins"
end

local function ApplyRemoteGameSettings(startRoll, minRoll, oneMeans, timeoutSeconds, betCopper, inviteScope)
    local db = DB()
    db.startRoll = startRoll or db.startRoll
    db.minRoll = minRoll or db.minRoll
    db.oneMeans = oneMeans or db.oneMeans
    db.timeoutSeconds = timeoutSeconds or db.timeoutSeconds
    if betCopper then
        local remaining = math.max(0, math.floor(tonumber(betCopper) or 0))
        db.betGold = math.floor(remaining / 10000)
        remaining = remaining - (db.betGold * 10000)
        db.betSilver = math.floor(remaining / 100)
        db.betCopper = remaining - (db.betSilver * 100)
    end
    if inviteScope and (inviteScope == "TARGET" or inviteScope == "PARTY" or inviteScope == "RAID") then db.inviteScope = inviteScope end
    NormalizeMoney()
end

local function BuildInviteSummary(offer)
    if not offer then return "No invitation details available." end
    local expected = tonumber(offer.expectedMax) or tonumber(offer.startRoll) or 0
    local minRoll = tonumber(offer.minRoll) or 1
    local timeoutSeconds = tonumber(offer.timeoutSeconds) or 0
    local lines = {}
    table.insert(lines, "Expected: /roll " .. tostring(minRoll) .. "-" .. tostring(expected))
    table.insert(lines, "Mode: " .. tostring(offer.gameMode or "REVERSE"))
    table.insert(lines, "Rule: " .. BuildOfferRuleLabel(offer.oneMeans))
    table.insert(lines, "Bet: " .. FormatMoney(offer.betCopper or 0) .. " per player (" .. tostring(offer.betMode or "POT") .. ")")
    table.insert(lines, "Timeout: " .. tostring(timeoutSeconds) .. "s")
    table.insert(lines, "Invite scope: " .. BuildScopeLabel(offer.inviteScope or "PARTY"))
    if offer.state and offer.state ~= "" then
        table.insert(lines, "State: " .. tostring(offer.state))
    end
    if offer.nextPlayer and offer.nextPlayer ~= "" then
        table.insert(lines, "Next: " .. tostring(offer.nextPlayer))
    end
    return table.concat(lines, "\n")
end

local function ShowInvitePopup(offer)
    if not offer then return end

    pendingOffer = offer

    local host = tostring(offer.host or "unknown")
    local summary = BuildInviteSummary(offer)

    Print("DeathRoll invite from " .. host .. ": " .. string.gsub(summary, "\n", "; "))

    if StaticPopup_Hide then
        StaticPopup_Hide("DEATHROLLMATE_JOIN")
    end

    local popup = nil
    if StaticPopup_Show then
        popup = StaticPopup_Show("DEATHROLLMATE_JOIN", host, summary, offer)
    end

    if not popup then
        Print("Invite popup could not be opened by the client UI. The invite is stored; use /dr join to request entry.")
    end
end

local function ClearSettlementEntries()
    ClearTable(settlementEntries)
end

local function AddSettlementEntry(fromPlayer, toPlayer, amountCopper, reason)
    fromPlayer = NormalizeName(fromPlayer)
    toPlayer = NormalizeName(toPlayer)
    amountCopper = math.max(0, math.floor(tonumber(amountCopper) or 0))
    if not fromPlayer or not toPlayer or amountCopper <= 0 then return end
    table.insert(settlementEntries, {
        from = fromPlayer,
        to = toPlayer,
        amount = amountCopper,
        reason = reason or "Bet settlement",
        paid = false,
    })
end

local function BuildSettlementEntryText(prefix)
    if #settlementEntries == 0 then return "No settlement." end
    local total = 0
    local lines = {}
    for i = 1, #settlementEntries do
        local e = settlementEntries[i]
        total = total + (tonumber(e.amount) or 0)
        table.insert(lines, tostring(e.from) .. " -> " .. tostring(e.to) .. ": " .. FormatMoney(e.amount))
    end
    local label = prefix or "Settlement"
    return label .. ": " .. table.concat(lines, "; ") .. " (total " .. FormatMoney(total) .. ")."
end

local function BuildWinnerSettlement(winner)
    ClearSettlementEntries()
    local bet = GetBetCopperValue()
    if bet <= 0 then return "No bet configured." end

    local payers = GetActiveParticipantNames(winner)
    if #payers <= 0 then return "No settlement: no other active participants." end

    local mode = DB().betMode or "POT"
    for i = 1, #payers do
        AddSettlementEntry(payers[i], winner, bet, mode == "POT" and "Pot contribution" or "Winner takes bet")
    end

    if mode == "POT" then
        return BuildSettlementEntryText("Settlement (pot " .. FormatMoney(bet * (#payers + 1)) .. ", winner net " .. FormatMoney(bet * #payers) .. ")")
    end

    return BuildSettlementEntryText("Settlement")
end

local function BuildLoserSettlement(loser)
    ClearSettlementEntries()
    local bet = GetBetCopperValue()
    if bet <= 0 then return "No bet configured." end

    local payees = GetActiveParticipantNames(loser)
    if #payees <= 0 then return "No settlement: no remaining active participants." end

    local mode = DB().betMode or "LOSER_PAYS"
    for i = 1, #payees do
        AddSettlementEntry(loser, payees[i], bet, mode == "POT" and "Timeout/loser payout" or "Loser pays bet")
    end

    return BuildSettlementEntryText("Settlement")
end

local function AddParticipant(player, status)
    if not player or player == "" then return nil end

    player = NormalizeName(player)
    if not participants[player] then
        participants[player] = {
            name = player,
            rolls = 0,
            last = nil,
            status = status or "Auto-joined",
            eliminated = false,
            accepted = status == "Accepted" or status == "Host" or false,
            requested = status == "Requested" or false,
        }
        table.insert(participantOrder, player)
    else
        if status and status ~= "" then
            participants[player].status = status
            if status == "Accepted" or status == "Host" then participants[player].accepted = true; participants[player].requested = false end
            if status == "Requested" then participants[player].requested = true end
        end
    end

    return participants[player]
end

local function AddHostParticipant()
    local me = NormalizeName(OwnName())
    local p = AddParticipant(me, "Host")
    if p then
        p.accepted = true
        p.requested = false
        p.eliminated = false
        p.status = "Host"
    end
    return p
end

local function AddHistory(player, roll, low, high, note)
    table.insert(history, {
        player = player,
        roll = roll,
        low = low,
        high = high,
        note = note,
    })

    while #history > 50 do
        table.remove(history, 1)
    end
end

SaveSessionSnapshot = function()
    local db = DB()
    if state == "IDLE" and #history == 0 and #participantOrder == 0 then
        db.lastSession = nil
        return
    end

    local partCopy = {}
    for name, data in pairs(participants) do partCopy[name] = CopyTableShallow(data) end
    local orderCopy = {}
    for i = 1, #participantOrder do orderCopy[i] = participantOrder[i] end
    local historyCopy = {}
    for i = 1, #history do historyCopy[i] = CopyTableShallow(history[i]) end
    local auditCopy = {}
    for i = 1, #auditLog do auditCopy[i] = auditLog[i] end

    db.lastSession = {
        version = VERSION,
        savedAt = time and time() or 0,
        state = state,
        currentMax = currentMax,
        lastPlayer = lastPlayer,
        lastRoll = lastRoll,
        lastRange = lastRange,
        warningText = warningText,
        resultText = resultText,
        nextPlayer = nextPlayer,
        hostName = hostName,
        remoteHost = remoteHost,
        gameId = gameId,
        participants = partCopy,
        participantOrder = orderCopy,
        history = historyCopy,
        auditLog = auditCopy,
    }
end

local function RestoreSessionSnapshot()
    local snapshot = DB().lastSession
    if type(snapshot) ~= "table" then
        Print("No saved Death Roll session is available.")
        return false
    end

    state = snapshot.state or "IDLE"
    currentMax = snapshot.currentMax
    lastPlayer = snapshot.lastPlayer
    lastRoll = snapshot.lastRoll
    lastRange = snapshot.lastRange
    warningText = snapshot.warningText
    resultText = snapshot.resultText
    nextPlayer = snapshot.nextPlayer
    hostName = snapshot.hostName
    remoteHost = snapshot.remoteHost
    gameId = snapshot.gameId
    StopTimeout()

    ClearTable(participants)
    ClearTable(participantOrder)
    ClearTable(history)
    ClearTable(auditLog)
    if type(snapshot.participants) == "table" then
        for name, data in pairs(snapshot.participants) do participants[name] = CopyTableShallow(data) end
    end
    if type(snapshot.participantOrder) == "table" then
        for i = 1, #snapshot.participantOrder do participantOrder[i] = snapshot.participantOrder[i] end
    end
    if type(snapshot.history) == "table" then
        for i = 1, #snapshot.history do history[i] = CopyTableShallow(snapshot.history[i]) end
    end
    if type(snapshot.auditLog) == "table" then
        for i = 1, #snapshot.auditLog do auditLog[i] = snapshot.auditLog[i] end
    end

    Audit("Session restored from SavedVariables")
    RefreshUI()
    Print("Previous Death Roll session restored.")
    return true
end

local function DiscardSessionSnapshot()
    DB().lastSession = nil
    Print("Saved Death Roll session discarded.")
end

local function GetExpectedMax()
    if state == "ARMED" then return DB().startRoll end
    if state == "ACTIVE" then return currentMax end
    return currentMax or DB().startRoll
end

local function BuildRuleLabel()
    if DB().oneMeans == "WIN" then return "min roll wins" end
    return "min roll loses"
end

local function IndexOfValue(list, value)
    for i = 1, #list do
        if list[i] == value then return i end
    end
    return 1
end

local function CycleSetting(key, values)
    local db = DB()
    local index = IndexOfValue(values, db[key]) + 1
    if index > #values then index = 1 end
    db[key] = values[index]
end

local function BuildReportLabel()
    local channel = DB().reportChannel or "AUTO"
    if channel == "SELF" then return "me" end
    return string.lower(channel)
end

BuildScopeLabel = function(scope)
    if scope == "SAY" then return "visible" end
    if scope == "TARGET" then return "target" end
    return string.lower(scope or "say")
end

local function GetAutoReportChannel()
    if GetNumRaidMembersSafe() > 0 then return "RAID" end
    if GetNumPartyMembersSafe() > 0 then return "PARTY" end
    return "SAY"
end

local function ResolveReportChannel()
    local configured = DB().reportChannel or "AUTO"
    if configured == "SELF" then return nil, nil end
    if configured == "AUTO" then return GetAutoReportChannel(), nil end
    if configured == "PARTY" and GetNumPartyMembersSafe() == 0 and GetNumRaidMembersSafe() == 0 then
        return nil, "Cannot report to PARTY because you are not in a party."
    end
    if configured == "RAID" and GetNumRaidMembersSafe() == 0 then
        return nil, "Cannot report to RAID because you are not in a raid."
    end
    return configured, nil
end

local function SafeSendChat(message)
    if not message or message == "" then return end

    local channel, errorMessage = ResolveReportChannel()
    if errorMessage then
        Print(errorMessage)
        Print(message)
        return
    end

    if not channel then
        Print(message)
        return
    end

    SendChatMessage(message, channel)
end

local function GetCommDistribution()
    if GetNumRaidMembersSafe() > 0 then return "RAID" end
    if GetNumPartyMembersSafe() > 0 then return "PARTY" end
    return nil
end

local function SendComm(message, target)
    local db = DB()
    if not db.commEnabled then return false, "Addon communication is disabled." end
    if not SendAddonMessage then return false, "SendAddonMessage is not available in this client." end
    if not message or message == "" then return false, "Empty addon communication message." end

    if target and target ~= "" then
        SendAddonMessage(COMM_PREFIX, message, "WHISPER", target)
        return true, "WHISPER"
    end

    local dist = GetCommDistribution()
    if dist then
        SendAddonMessage(COMM_PREFIX, message, dist)
        return true, dist
    end

    return false, "No PARTY or RAID addon communication channel is available. Join a group/raid or target a player for whisper-based addon invite."
end

local function SendCommDirect(message, distribution, target)
    local db = DB()
    if not db.commEnabled then return false, "Addon communication is disabled." end
    if not SendAddonMessage then return false, "SendAddonMessage is not available in this client." end
    if not message or message == "" then return false, "Empty addon communication message." end
    if not distribution or distribution == "" then return false, "Missing addon communication distribution." end

    if distribution == "WHISPER" then
        if not target or target == "" then return false, "Missing whisper target." end
        SendAddonMessage(COMM_PREFIX, message, "WHISPER", target)
        return true, "WHISPER"
    end

    SendAddonMessage(COMM_PREFIX, message, distribution)
    return true, distribution
end

local function GetOrCreateGameId()
    if not gameId then
        local stamp = time and time() or math.floor(GetTime() * 1000)
        gameId = NormalizeName(OwnName()) .. "-" .. tostring(stamp)
    end
    return gameId
end

local function EncodeText(text)
    text = tostring(text or "")
    text = string.gsub(text, "|", "/")
    text = string.gsub(text, "\n", " ")
    return text
end

local function SendStartComm()
    local db = DB()
    local gid = GetOrCreateGameId()
    local bet = tostring(GetBetCopperValue())
    SendComm("START|" .. gid .. "|" .. NormalizeName(OwnName()) .. "|" .. tostring(db.startRoll) .. "|" .. tostring(db.minRoll) .. "|" .. tostring(db.oneMeans) .. "|" .. tostring(db.timeoutSeconds) .. "|" .. bet .. "|" .. tostring(db.inviteScope))
end

local function GetTargetPlayerName()
    if UnitExists and UnitIsPlayer and UnitName and UnitExists("target") and UnitIsPlayer("target") then
        return NormalizeName(UnitName("target"))
    end
    return nil
end

local function AddInviteRecipient(recipients, seen, name)
    name = NormalizeName(name)
    if not name or name == "" then return end
    if NormalizeName(name) == NormalizeName(OwnName()) then return end
    if seen[name] then return end
    seen[name] = true
    table.insert(recipients, name)
end

local function GetKnownGroupInviteRecipients(scope)
    local recipients = {}
    local seen = {}
    scope = scope or "SAY"

    for i = 1, GetNumPartyMembersSafe() do
        local token = "party" .. tostring(i)
        if UnitExists(token) and UnitIsPlayer(token) then
            local name = NormalizeName(UnitName(token))
            if name and IsInScope(name, scope) then AddInviteRecipient(recipients, seen, name) end
        end
    end

    for i = 1, GetNumRaidMembersSafe() do
        local token = "raid" .. tostring(i)
        if UnitExists(token) and UnitIsPlayer(token) then
            local name = NormalizeName(UnitName(token))
            if name and IsInScope(name, scope) then AddInviteRecipient(recipients, seen, name) end
        end
    end

    local target = GetTargetPlayerName()
    if target and IsInScope(target, scope) then AddInviteRecipient(recipients, seen, target) end

    return recipients
end

local function SendWhisperOfferToRecipients(payload, recipients)
    local sent = false
    local channels = ""
    local errors = ""

    for i = 1, #recipients do
        local target = recipients[i]
        local ok, channelOrError = SendCommDirect(payload, "WHISPER", target)
        if ok then
            sent = true
            channels = channels .. (channels ~= "" and ", " or "") .. "WHISPER:" .. tostring(target)
        else
            errors = errors .. (errors ~= "" and "; " or "") .. tostring(channelOrError)
        end
    end

    return sent, channels, errors
end

local function SendOfferComm(target)
    local db = DB()
    local gid = GetOrCreateGameId()
    local bet = tostring(GetBetCopperValue())
    local offerState = state ~= "IDLE" and state ~= "DONE" and state or "ARMED"
    local expectedMax = GetExpectedMax() or db.startRoll
    local nextName = nextPlayer or ""
    local locked = db.lockParticipants and 1 or 0
    local scope = db.inviteScope or "PARTY"
    local payload = "OFFER|" .. gid .. "|" .. NormalizeName(OwnName()) .. "|" .. tostring(db.startRoll) .. "|" .. tostring(db.minRoll) .. "|" .. tostring(db.oneMeans) .. "|" .. tostring(db.timeoutSeconds) .. "|" .. bet .. "|" .. tostring(scope) .. "|" .. tostring(offerState) .. "|" .. tostring(expectedMax or 0) .. "|" .. tostring(nextName) .. "|" .. tostring(locked) .. "|" .. tostring(db.gameMode or "REVERSE") .. "|" .. tostring(db.betMode or "POT")

    local sent = false
    local channels = ""
    local errors = ""

    local function remember(ok, channelOrError)
        if ok then
            sent = true
            channels = channels .. (channels ~= "" and ", " or "") .. tostring(channelOrError)
        else
            errors = errors .. (errors ~= "" and "; " or "") .. tostring(channelOrError)
        end
    end

    -- Invite transport is intentionally explicit: TARGET / PARTY / RAID.
    -- Players without the addon will not see the popup, but they can still join
    -- by making a valid manual /roll, which is handled through CHAT_MSG_SYSTEM.
    if scope == "TARGET" then
        target = target or GetTargetPlayerName()
        if not target or target == "" then
            remember(false, "Invite scope is TARGET, but no player target is selected.")
        elseif NormalizeName(target) == NormalizeName(OwnName()) then
            AddHostParticipant()
            remember(false, "You are the host and already in the game. Target another player, or use PARTY/RAID invite scope.")
        else
            remember(SendCommDirect(payload, "WHISPER", target))
        end
    elseif scope == "PARTY" then
        if GetNumRaidMembersSafe() > 0 then
            local recipients = GetKnownGroupInviteRecipients("PARTY")
            local ok, ch, err = SendWhisperOfferToRecipients(payload, recipients)
            if ok then sent = true; channels = channels .. (channels ~= "" and ", " or "") .. ch end
            if err and err ~= "" then errors = errors .. (errors ~= "" and "; " or "") .. err end
        elseif GetNumPartyMembersSafe() > 0 then
            remember(SendCommDirect(payload, "PARTY"))
        else
            remember(false, "Invite scope is PARTY, but you are not in a party.")
        end
    elseif scope == "RAID" then
        if GetNumRaidMembersSafe() > 0 then
            remember(SendCommDirect(payload, "RAID"))
        else
            remember(false, "Invite scope is RAID, but you are not in a raid.")
        end
    else
        remember(false, "Invalid invite scope: " .. tostring(scope) .. ".")
    end

    if sent then return true, channels end
    if errors ~= "" then return false, errors end
    return false, "No addon invite recipients found for invite scope " .. BuildScopeLabel(scope) .. ". Players without the addon can still join by using /roll manually."
end

local function SendTurnComm()
    if state ~= "ACTIVE" and state ~= "ARMED" then return end
    local gid = GetOrCreateGameId()
    SendComm("TURN|" .. gid .. "|" .. state .. "|" .. tostring(GetExpectedMax() or 0) .. "|" .. tostring(nextPlayer or "") .. "|" .. tostring(DB().lockParticipants and 1 or 0))
end

local function SendResultComm(text)
    local gid = GetOrCreateGameId()
    SendComm("RESULT|" .. gid .. "|" .. EncodeText(text))
end

SendPlayerJoinedComm = function(player, status)
    if not IsLocalHost() then return end
    local gid = GetOrCreateGameId()
    SendComm("JOINED|" .. gid .. "|" .. tostring(NormalizeName(player) or "") .. "|" .. EncodeText(status or "Active"))
end

SendRollAcceptedComm = function(player, roll, low, high)
    if not IsLocalHost() then return end
    local gid = GetOrCreateGameId()
    SendComm("ROLL|" .. gid .. "|" .. tostring(NormalizeName(player) or "") .. "|" .. tostring(roll or 0) .. "|" .. tostring(low or 0) .. "|" .. tostring(high or 0) .. "|" .. tostring(currentMax or 0) .. "|" .. tostring(nextPlayer or "") .. "|" .. tostring(state or "ACTIVE") .. "|" .. tostring(DB().lockParticipants and 1 or 0))
end

SendRejectComm = function(player, reason, roll, low, high)
    if not IsLocalHost() then return end
    local gid = GetOrCreateGameId()
    SendComm("REJECT|" .. gid .. "|" .. tostring(NormalizeName(player) or "") .. "|" .. EncodeText(reason or "rejected") .. "|" .. tostring(roll or "") .. "|" .. tostring(low or "") .. "|" .. tostring(high or ""))
end

local function SendVersionCheck()
    versionPeers[NormalizeName(OwnName())] = VERSION
    local gid = GetOrCreateGameId()
    local ok, channelOrError = SendComm("HELLO|" .. tostring(gid) .. "|" .. VERSION)
    if ok then
        Print("Version check sent via " .. tostring(channelOrError) .. ".")
    else
        Print("Version check local only: " .. tostring(channelOrError))
    end
end

local function PrintVersionSummary()
    versionPeers[NormalizeName(OwnName())] = VERSION
    Print("Addon versions:")
    for name, ver in pairs(versionPeers) do
        local suffix = ver == VERSION and "" or " (different)"
        Print("- " .. tostring(name) .. ": " .. tostring(ver) .. suffix)
    end
end

local function BuildParticipantNames()
    if #participantOrder == 0 then return "none" end
    local text = ""
    for i = 1, #participantOrder do
        if i > 1 then text = text .. ", " end
        text = text .. participantOrder[i]
    end
    return text
end

local function EscapePattern(text)
    return string.gsub(text, "([%(%)%.%%%+%-%*%?%[%]%^%$])", "%%%1")
end

local localizedRollPattern = nil
local function BuildLocalizedRollPattern()
    if localizedRollPattern then return localizedRollPattern end
    if type(RANDOM_ROLL_RESULT) ~= "string" then return nil end

    local pattern = EscapePattern(RANDOM_ROLL_RESULT)
    pattern = string.gsub(pattern, "%%%%s", "(.+)")
    pattern = string.gsub(pattern, "%%%%d", function() return "(%d+)" end)
    localizedRollPattern = "^" .. pattern .. "$"
    return localizedRollPattern
end

local function ParseRollMessage(message)
    if not message or message == "" then return nil end

    local player, roll, low, high = string.match(message, "^(.+) rolls (%d+) %((%d+)%-(%d+)%)$")
    if player then return NormalizeName(player), tonumber(roll), tonumber(low), tonumber(high) end

    player, roll, low, high = string.match(message, "^(.+) rolls (%d+) %((%d+)%s*%-%s*(%d+)%)$")
    if player then return NormalizeName(player), tonumber(roll), tonumber(low), tonumber(high) end

    local pattern = BuildLocalizedRollPattern()
    if pattern then
        player, roll, low, high = string.match(message, pattern)
        if player then return NormalizeName(player), tonumber(roll), tonumber(low), tonumber(high) end
    end

    return nil
end

local function HideCountdown()
    if countdown.frame then countdown.frame:Hide() end
end

StopTimeout = function()
    timeoutDeadline = nil
    timeoutStartTime = nil
    timeoutTarget = nil
    timeoutKind = nil
    countdownLastSecond = nil
    HideCountdown()
end

local function IsLocalTimerAllowed()
    -- Remote START/TURN sync may arrive before the local player has accepted an invite.
    -- Do not start a countdown for a player who has not joined the remote game yet.
    if HasRemoteHost() and not IsJoinAccepted(OwnName()) then return false end
    return true
end

local function StartTimeout(target, kind)
    local db = DB()
    if not db.timeoutEnabled then StopTimeout(); return end

    local seconds = tonumber(db.timeoutSeconds) or 0
    if seconds <= 0 then StopTimeout(); return end
    if state == "DONE" or state == "IDLE" then StopTimeout(); return end
    if not IsLocalTimerAllowed() then StopTimeout(); return end

    timeoutStartTime = GetTime()
    timeoutDeadline = timeoutStartTime + seconds
    timeoutTarget = target
    timeoutKind = kind or "TURN"
    countdownLastSecond = nil
end

local function GetTimeoutRemaining()
    if not timeoutDeadline then return nil end
    local remaining = math.ceil(timeoutDeadline - GetTime())
    if remaining < 0 then remaining = 0 end
    return remaining
end

local function GetTimeoutFraction()
    if not timeoutDeadline or not timeoutStartTime then return 0 end
    local total = timeoutDeadline - timeoutStartTime
    if total <= 0 then return 0 end
    local remaining = timeoutDeadline - GetTime()
    if remaining < 0 then remaining = 0 end
    if remaining > total then remaining = total end
    return remaining / total
end

local function BuildTimeoutLabel()
    local remaining = GetTimeoutRemaining()
    if not remaining then
        if DB().timeoutEnabled then return "Roll timeout: " .. tostring(DB().timeoutSeconds or 10) .. "s" end
        return "Roll timeout: off"
    end

    if timeoutKind == "FIRST" then return "First roll timeout: " .. tostring(remaining) .. "s" end
    if timeoutKind == "JOIN" then return "Roll timeout: " .. tostring(remaining) .. "s" end
    if timeoutTarget then return "Turn timeout: " .. tostring(timeoutTarget) .. " - " .. tostring(remaining) .. "s" end
    return "Roll timeout: " .. tostring(remaining) .. "s"
end

local function ResetSession(keepArmed)
    state = keepArmed and "ARMED" or "IDLE"
    currentMax = keepArmed and DB().startRoll or nil
    lastPlayer = nil
    lastRoll = nil
    lastRange = nil
    warningText = nil
    resultText = nil
    nextPlayer = nil
    StopTimeout()
    pendingOffer = nil
    pendingJoinRequest = nil
    ClearTable(participants)
    ClearTable(participantOrder)
    ClearTable(history)
end

local function EndGame(message, settlement)
    state = "DONE"
    StopTimeout()
    resultText = message
    if settlement and settlement ~= "" then
        resultText = resultText .. " " .. settlement
    end

    Audit(resultText)
    PlayFeedbackSound("result")
    Print(resultText)
    SendResultComm(resultText)
    if DB().autoReportResult then
        SafeSendChat("[DeathRoll] " .. resultText)
    end
    SaveSessionSnapshot()
    if ShowSettlementPanel and #settlementEntries > 0 then ShowSettlementPanel() end
end

local function EliminatePlayer(player, reason)
    player = NormalizeName(player)
    if not player or not participants[player] then return end
    participants[player].eliminated = true
    participants[player].status = reason or "Eliminated"
    AddHistory(player, "TIMEOUT", "-", "-", reason or "Eliminated")
end

local function HandleTimeoutExpired()
    local expiredTarget = timeoutTarget
    StopTimeout()
    PlayFeedbackSound("timeout")

    if state == "ARMED" then
        if CountParticipants() == 0 then
            state = "IDLE"
            SetWarning("Roll timeout expired. No valid first roll received.")
        else
            state = "ACTIVE"
            currentMax = currentMax or DB().startRoll
            if CountActiveParticipants() >= 2 then
                DB().lockParticipants = true
                nextPlayer = FindNextActivePlayerAfter(lastPlayer or participantOrder[1])
                SetWarning("Join window expired. Participants locked: " .. BuildParticipantNames() .. ". Next: " .. tostring(nextPlayer or "-") .. ".")
                StartTimeout(nextPlayer, "TURN")
                SendTurnComm()
            else
                SetWarning("Join window expired, but only one participant joined. Game cancelled.")
                state = "IDLE"
            end
        end
        SaveSessionSnapshot()
        RefreshUI()
        return
    end

    if state ~= "ACTIVE" then RefreshUI(); return end

    if not DB().lockParticipants then
        if CountActiveParticipants() >= 2 then
            DB().lockParticipants = true
            if not expiredTarget then expiredTarget = FindNextActivePlayerAfter(lastPlayer or participantOrder[1]) end
            SetWarning("Timeout expired. Participants locked: " .. BuildParticipantNames() .. ".")
        else
            SetWarning("Join window expired, but only one participant joined. Game cancelled.")
            state = "IDLE"
            RefreshUI()
            return
        end
    end

    local loser = expiredTarget or nextPlayer
    if not loser or not participants[loser] or participants[loser].eliminated then
        loser = FindNextActivePlayerAfter(lastPlayer or participantOrder[1])
    end

    if loser then
        local settlement = BuildLoserSettlement(loser)
        EliminatePlayer(loser, "Timed out")
        local remaining = CountActiveParticipants()

        if remaining <= 0 then
            EndGame(loser .. " timed out and loses.", settlement)
        elseif remaining == 1 then
            local winner = GetActiveParticipantNames(nil)[1]
            EndGame(loser .. " timed out and loses. " .. tostring(winner) .. " wins.", settlement)
        else
            resultText = loser .. " timed out and is eliminated. " .. settlement
            Print(resultText)
            SendResultComm(resultText)
            if DB().autoReportResult then SafeSendChat("[DeathRoll] " .. resultText) end
            nextPlayer = FindNextActivePlayerAfter(loser)
            StartTimeout(nextPlayer, "TURN")
            SendTurnComm()
            SaveSessionSnapshot()
        end
    else
        SetWarning("Roll timeout expired, but no expected player could be resolved.")
    end

    SaveSessionSnapshot()
    RefreshUI()
end

local STYLE = {
    bg = { 0.035, 0.035, 0.035, 0.94 },
    bg2 = { 0.075, 0.075, 0.075, 0.88 },
    border = { 0.20, 0.20, 0.20, 1.00 },
    borderLight = { 0.42, 0.34, 0.18, 1.00 },
    text = { 0.88, 0.88, 0.84, 1.00 },
    muted = { 0.62, 0.62, 0.58, 1.00 },
    accent = { 0.92, 0.72, 0.32, 1.00 },
    danger = { 0.80, 0.22, 0.18, 1.00 },
}

local function ApplyBackdrop(frame, variant)
    if not frame or not frame.SetBackdrop then return end
    frame:SetBackdrop({
        bgFile = "Interface\\Buttons\\WHITE8X8",
        edgeFile = "Interface\\Buttons\\WHITE8X8",
        tile = false,
        edgeSize = 1,
        insets = { left = 1, right = 1, top = 1, bottom = 1 },
    })

    local bg = variant == "panel" and STYLE.bg2 or STYLE.bg
    frame:SetBackdropColor(bg[1], bg[2], bg[3], bg[4])
    frame:SetBackdropBorderColor(STYLE.border[1], STYLE.border[2], STYLE.border[3], STYLE.border[4])
end

local function ApplyAccentBorder(frame)
    if not frame or not frame.SetBackdropBorderColor then return end
    frame:SetBackdropBorderColor(STYLE.borderLight[1], STYLE.borderLight[2], STYLE.borderLight[3], STYLE.borderLight[4])
end

local function SetFontColor(fontString, color)
    if not fontString then return end
    color = color or STYLE.text
    fontString:SetTextColor(color[1], color[2], color[3], color[4])
end

local function CreateSectionTitle(parent, text, x, y, width)
    local label = parent:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    label:SetPoint("TOPLEFT", parent, "TOPLEFT", x, y)
    label:SetWidth(width or 320)
    label:SetJustifyH("LEFT")
    label:SetText(string.upper(text or ""))
    SetFontColor(label, STYLE.accent)
    return label
end

local function CreatePanel(parent, x, y, width, height)
    local panel = CreateFrame("Frame", nil, parent)
    panel:SetPoint("TOPLEFT", parent, "TOPLEFT", x, y)
    panel:SetWidth(width)
    panel:SetHeight(height)
    ApplyBackdrop(panel, "panel")
    return panel
end

local function SaveCountdownPosition()
    if not countdown.frame then return end
    local point, _, relativePoint, xOfs, yOfs = countdown.frame:GetPoint(1)
    local db = DB()
    db.countdownPoint = point or "CENTER"
    db.countdownRelativePoint = relativePoint or "CENTER"
    db.countdownX = xOfs or 0
    db.countdownY = yOfs or 170
end

local function CreateCountdownUI()
    if countdown.frame then return end

    local db = DB()
    local frame = CreateFrame("Frame", "DeathRollMateCountdownFrame", UIParent)
    countdown.frame = frame
    frame:SetWidth(360)
    frame:SetHeight(58)
    frame:SetPoint(db.countdownPoint or "CENTER", UIParent, db.countdownRelativePoint or "CENTER", db.countdownX or 0, db.countdownY or 170)
    frame:SetMovable(true)
    frame:EnableMouse(true)
    frame:RegisterForDrag("LeftButton")
    frame:SetClampedToScreen(true)
    frame:SetScript("OnDragStart", function(self)
        if not DB().lockFrame then self:StartMoving() end
    end)
    frame:SetScript("OnDragStop", function(self)
        self:StopMovingOrSizing()
        SaveCountdownPosition()
    end)
    ApplyBackdrop(frame, "main")
    ApplyAccentBorder(frame)

    local title = frame:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    countdown.title = title
    title:SetPoint("TOPLEFT", frame, "TOPLEFT", 12, -8)
    title:SetWidth(245)
    title:SetJustifyH("LEFT")
    SetFontColor(title, STYLE.muted)
    title:SetText("DEATH ROLL TIMER")

    local timer = frame:CreateFontString(nil, "OVERLAY", "GameFontNormalLarge")
    countdown.timer = timer
    timer:SetPoint("TOPRIGHT", frame, "TOPRIGHT", -12, -4)
    timer:SetWidth(70)
    timer:SetJustifyH("RIGHT")
    timer:SetText("10")
    SetFontColor(timer, STYLE.accent)

    local barBg = CreateFrame("Frame", nil, frame)
    countdown.barBg = barBg
    barBg:SetPoint("BOTTOMLEFT", frame, "BOTTOMLEFT", 10, 10)
    barBg:SetWidth(340)
    barBg:SetHeight(22)
    ApplyBackdrop(barBg, "panel")

    local bar = CreateFrame("StatusBar", nil, barBg)
    countdown.bar = bar
    bar:SetPoint("TOPLEFT", barBg, "TOPLEFT", 2, -2)
    bar:SetWidth(336)
    bar:SetHeight(18)
    bar:SetStatusBarTexture("Interface\\TargetingFrame\\UI-StatusBar")
    bar:SetMinMaxValues(0, 1)
    bar:SetValue(1)
    bar:SetStatusBarColor(STYLE.accent[1], STYLE.accent[2], STYLE.accent[3])

    local sub = bar:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    countdown.sub = sub
    sub:SetPoint("CENTER", bar, "CENTER", 0, 0)
    sub:SetWidth(326)
    sub:SetJustifyH("CENTER")
    sub:SetText("")
    SetFontColor(sub, STYLE.text)

    frame:Hide()
end

local function UpdateCountdownUI()
    if not DB().showCountdown then HideCountdown(); return end
    if not timeoutDeadline then HideCountdown(); return end

    CreateCountdownUI()
    local remaining = GetTimeoutRemaining() or 0
    countdown.bar:SetValue(GetTimeoutFraction())

    if countdownLastSecond ~= remaining then
        countdownLastSecond = remaining
        if remaining > 0 and remaining <= 3 then PlayFeedbackSound("warn") end
    end

    if remaining <= 3 then
        countdown.bar:SetStatusBarColor(STYLE.danger[1], STYLE.danger[2], STYLE.danger[3])
        SetFontColor(countdown.timer, STYLE.danger)
    else
        countdown.bar:SetStatusBarColor(STYLE.accent[1], STYLE.accent[2], STYLE.accent[3])
        SetFontColor(countdown.timer, STYLE.accent)
    end

    countdown.timer:SetText(tostring(remaining))

    local expected = "/roll " .. tostring(DB().minRoll) .. "-" .. tostring(GetExpectedMax())

    if timeoutKind == "FIRST" then
        countdown.title:SetText("WAITING FOR FIRST ROLL")
        countdown.sub:SetText("Expected: " .. expected)
    elseif timeoutTarget then
        countdown.title:SetText("ROLL NOW: " .. tostring(timeoutTarget))
        countdown.sub:SetText("Expected: " .. expected .. "   Timeout = loss")
    else
        countdown.title:SetText("ROLL TIMER")
        countdown.sub:SetText("Expected: " .. expected)
    end

    countdown.frame:Show()
end

local function BuildCommLabel()
    if DB().commEnabled then return "Comm: on" end
    return "Comm: off"
end

local function BuildHostLabel()
    if hostName then return "Host: " .. tostring(hostName) end
    if remoteHost then return "Host: " .. tostring(remoteHost) .. " (remote)" end
    return "Host: -"
end

RefreshUI = function()
    if ui.frame then
        local db = DB()
        local expected = GetExpectedMax()
        local expectedText = expected and ("/roll " .. tostring(db.minRoll) .. "-" .. tostring(expected)) or "-"
        local nextText = nextPlayer or (db.lockParticipants and "-" or "any valid roller")
        local statusText = "Idle"
        if state == "ARMED" then statusText = "Waiting for first roll"
        elseif state == "ACTIVE" then statusText = "Game active"
        elseif state == "DONE" then statusText = "Finished" end

        ui.title:SetText("DeathRollMate " .. VERSION)
        ui.status:SetText(statusText)
        ui.expected:SetText("Roll: " .. expectedText)
        ui.next:SetText("Next: " .. tostring(nextText))
        ui.timeout:SetText(BuildTimeoutLabel())
        ui.bet:SetText(BuildRuleLabel() .. "    " .. BuildBetLabel())
        ui.last:SetText(lastPlayer and ("Last: " .. lastPlayer .. " rolled " .. tostring(lastRoll) .. " " .. (lastRange or "")) or "Last: -")

        if resultText then ui.result:SetText(resultText)
        elseif warningText then ui.result:SetText(warningText)
        else ui.result:SetText("Ready.") end

        if not ui.startBox:HasFocus() then ui.startBox:SetText(tostring(db.startRoll or 1000)) end
        if not ui.minBox:HasFocus() then ui.minBox:SetText(tostring(db.minRoll or 1)) end
        if not ui.timeoutBox:HasFocus() then ui.timeoutBox:SetText(tostring(db.timeoutSeconds or 10)) end
        if not ui.betGoldBox:HasFocus() then ui.betGoldBox:SetText(tostring(db.betGold or 0)) end
        if not ui.betSilverBox:HasFocus() then ui.betSilverBox:SetText(tostring(db.betSilver or 0)) end
        if not ui.betCopperBox:HasFocus() then ui.betCopperBox:SetText(tostring(db.betCopper or 0)) end

        ui.autoJoin:SetChecked(db.autoJoin and true or false)
        ui.validateRange:SetChecked(db.validateRange and true or false)
        ui.lockPlayers:SetChecked(db.lockParticipants and true or false)
        ui.lockFrame:SetChecked(db.lockFrame and true or false)
        ui.timeoutEnabled:SetChecked(db.timeoutEnabled and true or false)
        ui.showCountdown:SetChecked(db.showCountdown and true or false)
        ui.autoReportResult:SetChecked(db.autoReportResult and true or false)
        ui.commEnabled:SetChecked(db.commEnabled and true or false)
        ui.acceptRemoteSync:SetChecked(db.acceptRemoteSync and true or false)
        ui.requireJoinRequest:SetChecked(db.requireJoinRequest and true or false)
        if ui.soundEnabled then ui.soundEnabled:SetChecked(db.soundEnabled and true or false) end
        if ui.minimapEnabled then ui.minimapEnabled:SetChecked(db.minimapEnabled and true or false) end

        ui.ruleButton:SetText(db.oneMeans == "WIN" and "1 wins" or "1 loses")
        if ui.modeButton then ui.modeButton:SetText("Mode: " .. BuildGameModeLabel()) end
        if ui.betModeButton then ui.betModeButton:SetText("Bet mode: " .. BuildBetModeLabel()) end
        if ui.versionSummary then ui.versionSummary:SetText("Addon peers: " .. tostring((function() local c=0; for _ in pairs(versionPeers) do c=c+1 end; return c end)())) end
        ui.reportButton:SetText("Report: " .. BuildReportLabel())
        ui.watchButton:SetText("Watch: " .. BuildScopeLabel(db.watchScope))
        ui.inviteButton:SetText("Invite: " .. BuildScopeLabel(db.inviteScope))
        if ui.gameJoinButton then
            if HasRemoteHost() or (pendingOffer and pendingOffer.host) then
                ui.gameJoinButton:SetText("Request")
            else
                ui.gameJoinButton:SetText("Join")
            end
        end

        local participantCount = #participantOrder
        local participantContentHeight = math.max(96, (math.max(participantCount, 1) * 16) + 6)
        ui.participantContent:SetHeight(participantContentHeight)

        for i = 1, #ui.participantLines do
            local name = participantOrder[i]
            local line = ui.participantLines[i]
            if name and participants[name] then
                local p = participants[name]
                local status = p.status or "Active"
                if p.eliminated then status = status .. "/OUT" end
                line:SetText(i .. ". " .. name .. "   Rolls: " .. tostring(p.rolls) .. "   Last: " .. tostring(p.last or "-") .. "   " .. status)
                line:Show()
            elseif i == 1 and participantCount == 0 then
                line:SetText("No participants yet.")
                line:Show()
            else
                line:SetText("")
                line:Hide()
            end
        end

        local historyCount = #history
        local historyContentHeight = math.max(80, (math.max(historyCount, 1) * 16) + 6)
        ui.historyContent:SetHeight(historyContentHeight)

        for i = 1, #ui.historyLines do
            local row = history[i]
            local line = ui.historyLines[i]
            if row then
                if row.note then
                    line:SetText(i .. ". " .. row.player .. " - " .. tostring(row.note))
                else
                    line:SetText(i .. ". " .. row.player .. " rolled " .. tostring(row.roll) .. "  (" .. tostring(row.low) .. "-" .. tostring(row.high) .. ")")
                end
                line:Show()
            else
                line:SetText("")
                line:Hide()
            end
        end
    end

    if UpdateMinimapButton then UpdateMinimapButton() end
    UpdateCountdownUI()
end

local function SavePosition()
    if not ui.frame then return end
    local point, _, relativePoint, xOfs, yOfs = ui.frame:GetPoint(1)
    local db = DB()
    db.point = point or "CENTER"
    db.relativePoint = relativePoint or "CENTER"
    db.x = xOfs or 0
    db.y = yOfs or 0
end

local function ApplySettingsFromUI()
    if not ui.frame then return end

    local db = DB()
    local startRoll = tonumber(ui.startBox:GetText()) or 1000
    local minRoll = tonumber(ui.minBox:GetText()) or 1
    local timeoutSeconds = tonumber(ui.timeoutBox:GetText()) or 10
    local betGold = tonumber(ui.betGoldBox:GetText()) or 0
    local betSilver = tonumber(ui.betSilverBox:GetText()) or 0
    local betCopper = tonumber(ui.betCopperBox:GetText()) or 0

    if startRoll < 2 then startRoll = 1000 end
    if minRoll < 1 then minRoll = 1 end
    if minRoll >= startRoll then minRoll = 1 end
    if timeoutSeconds < 0 then timeoutSeconds = 10 end
    if betGold < 0 then betGold = 0 end
    if betSilver < 0 then betSilver = 0 end
    if betCopper < 0 then betCopper = 0 end

    db.startRoll = math.floor(startRoll)
    db.minRoll = math.floor(minRoll)
    db.timeoutSeconds = math.floor(timeoutSeconds)
    db.betGold = math.floor(betGold)
    db.betSilver = math.floor(betSilver)
    db.betCopper = math.floor(betCopper)
    NormalizeMoney()

    db.autoJoin = ui.autoJoin:GetChecked() and true or false
    db.validateRange = ui.validateRange:GetChecked() and true or false
    db.lockParticipants = ui.lockPlayers:GetChecked() and true or false
    db.lockFrame = ui.lockFrame:GetChecked() and true or false
    db.timeoutEnabled = ui.timeoutEnabled:GetChecked() and true or false
    db.showCountdown = ui.showCountdown:GetChecked() and true or false
    db.autoReportResult = ui.autoReportResult:GetChecked() and true or false
    db.commEnabled = ui.commEnabled:GetChecked() and true or false
    db.acceptRemoteSync = ui.acceptRemoteSync:GetChecked() and true or false
    db.requireJoinRequest = ui.requireJoinRequest:GetChecked() and true or false
    if ui.soundEnabled then db.soundEnabled = ui.soundEnabled:GetChecked() and true or false end
    if ui.minimapEnabled then db.minimapEnabled = ui.minimapEnabled:GetChecked() and true or false end

    if not db.timeoutEnabled or (db.timeoutSeconds or 0) <= 0 then
        StopTimeout()
    end

    if state == "ACTIVE" then
        if db.lockParticipants then
            if not nextPlayer and CountActiveParticipants() > 0 then
                nextPlayer = FindNextActivePlayerAfter(lastPlayer or participantOrder[1])
            end
            if timeoutDeadline then StartTimeout(nextPlayer, "TURN") end
        else
            if CountActiveParticipants() >= 2 then
                if not nextPlayer then nextPlayer = FindNextActivePlayerAfter(lastPlayer or participantOrder[1]) end
                if timeoutDeadline then StartTimeout(nextPlayer, "TURN") end
            else
                nextPlayer = nil
                if timeoutDeadline then StartTimeout(nil, "JOIN") end
            end
        end
    end
end

local function NewGame()
    ApplySettingsFromUI()
    local db = DB()
    db.lockParticipants = false
    ResetSession(true)
    hostName = NormalizeName(OwnName())
    AddHostParticipant()
    remoteHost = nil
    gameId = nil
    resultText = nil
    SetWarning("Waiting for first valid roll: /roll " .. tostring(db.minRoll) .. "-" .. tostring(db.startRoll))
    Audit("New game armed by " .. tostring(hostName) .. ", start " .. tostring(db.startRoll))
    StopTimeout()
    SendStartComm()
    SaveSessionSnapshot()
    RefreshUI()
end

local function ResetAll()
    DB().lockParticipants = false
    ResetSession(false)
    hostName = nil
    remoteHost = nil
    gameId = nil
    SetWarning(nil)
    resultText = nil
    ClearSettlementEntries()
    DB().lastSession = nil
    RefreshUI()
end

local function RollNow()
    ApplySettingsFromUI()

    if state == "IDLE" or state == "DONE" then
        DB().lockParticipants = false
        ResetSession(true)
        hostName = NormalizeName(OwnName())
        AddHostParticipant()
        remoteHost = nil
        gameId = nil
        SendStartComm()
    end

    local expected = GetExpectedMax()
    if not expected or expected < DB().minRoll then
        SetWarning("No valid expected max. Start a new game first.")
        RefreshUI()
        return
    end

    RandomRoll(DB().minRoll, expected)
end

local function Announce()
    local db = DB()

    if state == "IDLE" then
        SafeSendChat("[DeathRoll] New game available. Start roll: " .. tostring(db.startRoll) .. ". Rule: " .. BuildRuleLabel() .. ". " .. BuildBetLabel() .. ". Invite: " .. BuildScopeLabel(db.inviteScope) .. ". Manual /roll join is allowed if the roll is valid.")
        return
    end

    if state == "DONE" and resultText then
        SafeSendChat("[DeathRoll] " .. resultText)
        return
    end

    local expected = GetExpectedMax()
    SafeSendChat("[DeathRoll] Current max: " .. tostring(expected) .. ". Next: " .. tostring(nextPlayer or "any valid roller") .. " /roll " .. tostring(db.minRoll) .. "-" .. tostring(expected) .. ". Rule: " .. BuildRuleLabel() .. ". " .. BuildBetLabel() .. ".")
end

local function PrepareGameForInvite()
    ApplySettingsFromUI()
    if state == "IDLE" or state == "DONE" then
        DB().lockParticipants = false
        ResetSession(true)
        hostName = NormalizeName(OwnName())
        AddHostParticipant()
        remoteHost = nil
        gameId = nil
        resultText = nil
        SetWarning("Invite prepared. Waiting for accepted players; no roll timer is running yet.")
        Audit("Invite prepared by host")
        StopTimeout()
        SaveSessionSnapshot()
    end
end

local function Invite()
    ApplySettingsFromUI()
    PrepareGameForInvite()

    local target = GetTargetPlayerName()
    local sent, channel = SendOfferComm(target)
    if sent then
        if DB().inviteScope == "TARGET" and target then
            Print("Invite sent via addon communication. Invite: " .. BuildScopeLabel(DB().inviteScope) .. ". Channels: " .. tostring(channel) .. ". Target: " .. tostring(target) .. ".")
        else
            Print("Invite sent via addon communication. Invite: " .. BuildScopeLabel(DB().inviteScope) .. ". Channels: " .. tostring(channel) .. ".")
        end
    else
        Print("Invite was not sent: " .. tostring(channel))
        Print("Use Announce for a human-readable chat message, or join a party/raid / target a player who has the addon.")
    end
    RefreshUI()
end

local function ToggleRule()
    ApplySettingsFromUI()
    DB().oneMeans = DB().oneMeans == "WIN" and "LOSE" or "WIN"
    RefreshUI()
end

local function ToggleReportChannel()
    ApplySettingsFromUI()
    CycleSetting("reportChannel", REPORT_CHANNELS)
    RefreshUI()
end

local function ToggleWatchScope()
    ApplySettingsFromUI()
    CycleSetting("watchScope", WATCH_SCOPES)
    RefreshUI()
end

local function ToggleInviteScope()
    ApplySettingsFromUI()
    CycleSetting("inviteScope", INVITE_SCOPES)
    RefreshUI()
end

BuildGameModeLabel = function()
    local mode = DB().gameMode or "REVERSE"
    if mode == "CLASSIC" then return "Classic" end
    if mode == "ELIMINATION" then return "Elimination" end
    if mode == "FREE" then return "Free" end
    return "Reverse"
end

BuildBetModeLabel = function()
    local mode = DB().betMode or "POT"
    if mode == "WINNER_TAKES" then return "Winner takes" end
    if mode == "LOSER_PAYS" then return "Loser pays" end
    return "Pot"
end

local function ApplyGameModePreset(mode)
    local db = DB()
    mode = mode or db.gameMode or "REVERSE"
    db.gameMode = mode
    db.autoJoin = true
    db.validateRange = true
    db.timeoutEnabled = true
    db.timeoutSeconds = db.timeoutSeconds and db.timeoutSeconds > 0 and db.timeoutSeconds or 10

    if mode == "CLASSIC" then
        db.oneMeans = "LOSE"
        db.betMode = "LOSER_PAYS"
    elseif mode == "ELIMINATION" then
        db.oneMeans = "LOSE"
        db.betMode = "LOSER_PAYS"
    elseif mode == "FREE" then
        db.oneMeans = "WIN"
        db.betMode = "POT"
        db.timeoutEnabled = false
        db.lockParticipants = false
    else
        db.oneMeans = "WIN"
        db.betMode = "POT"
    end
end

local function ToggleGameMode()
    ApplySettingsFromUI()
    CycleSetting("gameMode", GAME_MODES)
    ApplyGameModePreset(DB().gameMode)
    RefreshUI()
end

local function ToggleBetMode()
    ApplySettingsFromUI()
    CycleSetting("betMode", BET_MODES)
    RefreshUI()
end

local function AddMe()
    AddParticipant(OwnName(), "Accepted")
    RefreshUI()
end

local function AddTarget()
    if UnitExists("target") and UnitIsPlayer("target") then
        AddParticipant(UnitName("target"), "Accepted")
        RefreshUI()
    else
        SetWarning("Target is not a player.")
        RefreshUI()
    end
end

local function RejectRoll(player, reason, roll, low, high)
    local rangeText = ""
    if roll and low and high then
        rangeText = " rolled " .. tostring(roll) .. " (" .. tostring(low) .. "-" .. tostring(high) .. ")"
    end
    local text = "Rejected roll from " .. tostring(player) .. ": " .. tostring(reason) .. "."
    SetWarning(text)
    AddHistory(player, roll or "-", low or "-", high or "-", "Rejected: " .. tostring(reason))
    Audit(text .. rangeText)
    PlayFeedbackSound("warn")
    SendRejectComm(player, reason, roll, low, high)
    SaveSessionSnapshot()
    RefreshUI()
end

local function HandleRoll(player, roll, low, high)
    player = NormalizeName(player)
    if state == "IDLE" or state == "DONE" then return end

    -- Host-authoritative model: remote clients wait for ROLL/REJECT/RESULT sync
    -- from the host instead of accepting visible combat-log/system rolls locally.
    if HasRemoteHost() and not IsLocalHost() then return end

    if not IsRollInWatchScope(player) then return end

    local db = DB()
    local expectedMax = GetExpectedMax()

    if db.validateRange then
        if low ~= db.minRoll or high ~= expectedMax then
            RejectRoll(player, "wrong range, expected /roll " .. tostring(db.minRoll) .. "-" .. tostring(expectedMax), roll, low, high)
            return
        end
    end

    if participants[player] and participants[player].eliminated then
        RejectRoll(player, "player is eliminated", roll, low, high)
        return
    end

    if db.lockParticipants then
        if not participants[player] then
            RejectRoll(player, "participants are locked", roll, low, high)
            return
        end
        if nextPlayer and NormalizeName(player) ~= NormalizeName(nextPlayer) then
            RejectRoll(player, "not your turn; expected " .. tostring(nextPlayer), roll, low, high)
            return
        end
    end

    local wasNewParticipant = not participants[player]
    if not participants[player] then
        if not db.autoJoin then
            RejectRoll(player, "not a participant and auto-join is disabled", roll, low, high)
            return
        end
        if not IsJoinEligible(player) then
            RejectRoll(player, "not eligible for manual roll entry", roll, low, high)
            return
        end
        AddParticipant(player, "Auto-joined")
        SendPlayerJoinedComm(player, "Auto-joined")
    end

    local p = AddParticipant(player, "Active")
    p.rolls = p.rolls + 1
    p.last = roll
    p.status = "Active"
    p.accepted = true
    p.requested = false

    lastPlayer = player
    lastRoll = roll
    lastRange = "(" .. tostring(low) .. "-" .. tostring(high) .. ")"
    warningText = nil
    AddHistory(player, roll, low, high, wasNewParticipant and "Accepted + auto-joined" or nil)
    Audit("Accepted roll: " .. player .. " rolled " .. tostring(roll) .. " (" .. tostring(low) .. "-" .. tostring(high) .. ")")

    if roll <= db.minRoll then
        currentMax = roll
        if db.oneMeans == "WIN" then
            EndGame(player .. " wins by rolling " .. tostring(roll) .. ".", BuildWinnerSettlement(player))
        else
            local settlement = BuildLoserSettlement(player)
            EliminatePlayer(player, "Rolled minimum")
            local remaining = CountActiveParticipants()
            if remaining == 1 then
                local winner = GetActiveParticipantNames(nil)[1]
                EndGame(player .. " loses by rolling " .. tostring(roll) .. ". " .. tostring(winner) .. " wins.", settlement)
            else
                EndGame(player .. " loses by rolling " .. tostring(roll) .. ".", settlement)
            end
        end
        RefreshUI()
        return
    end

    state = "ACTIVE"
    currentMax = roll
    resultText = nil

    if db.lockParticipants then
        nextPlayer = FindNextActivePlayerAfter(player)
        StartTimeout(nextPlayer, "TURN")
    else
        if CountActiveParticipants() >= 2 then
            nextPlayer = FindNextActivePlayerAfter(player)
            StartTimeout(nextPlayer, "TURN")
        else
            nextPlayer = nil
            StartTimeout(nil, "JOIN")
        end
    end

    SendRollAcceptedComm(player, roll, low, high)
    SendTurnComm()
    SaveSessionSnapshot()
    RefreshUI()
end

local function JoinLocalSelf(reason)
    local db = DB()

    if state == "IDLE" or state == "DONE" then
        SetWarning("No active Death Roll game to join. Start with New Game or wait for an invite.")
        RefreshUI()
        return false
    end

    local me = NormalizeName(OwnName())

    if participants[me] then
        participants[me].accepted = true
        participants[me].requested = false
        participants[me].status = reason or "Accepted"
        SetWarning("You are already in this Death Roll game.")
        RefreshUI()
        return true
    end

    if db.lockParticipants then
        SetWarning("Cannot join: participants are locked.")
        RefreshUI()
        return false
    end

    if not IsJoinEligible(me) then
        SetWarning("Cannot join by button right now. Players can always join by making a valid manual /roll while the game is accepting rolls.")
        RefreshUI()
        return false
    end

    AddParticipant(me, reason or "Accepted")
    SetWarning("You joined the Death Roll game.")

    if state == "ARMED" then
        currentMax = currentMax or db.startRoll
        StopTimeout()
    elseif state == "ACTIVE" then
        if CountActiveParticipants() >= 2 then
            if not nextPlayer then nextPlayer = FindNextActivePlayerAfter(lastPlayer or me) end
        end
        -- Joining must not reset the current roll timer.
    end

    SendTurnComm()
    RefreshUI()
    return true
end

local function SendJoinRequest()
    local target = nil
    if pendingOffer and pendingOffer.host then target = pendingOffer.host end
    if not target and HasRemoteHost() then target = remoteHost end

    if target then
        if NormalizeName(target) == NormalizeName(OwnName()) and IsLocalHost() then
            JoinLocalSelf("Accepted")
            return
        end

        local gid = pendingOffer and pendingOffer.gameId or gameId or "-"
        local ok, channelOrError = SendComm("JOINREQ|" .. tostring(gid) .. "|" .. NormalizeName(OwnName()), target)
        if ok then
            AddParticipant(OwnName(), "Requested")
            Print("Join request sent to " .. tostring(target) .. " (" .. tostring(channelOrError) .. ").")
        else
            Print("Join request was not sent: " .. tostring(channelOrError))
        end
        RefreshUI()
        return
    end

    if IsLocalHost() or (state ~= "IDLE" and state ~= "DONE" and not HasRemoteHost()) then
        JoinLocalSelf("Accepted")
        return
    end

    Print("No remote host known. Ask the host to press Invite, or start a local game with New Game.")
end


local function SplitPipe(text)
    local result = {}
    text = tostring(text or "")
    for part in string.gmatch(text .. "|", "(.-)|") do
        table.insert(result, part)
    end
    return result
end

local function AcceptJoinRequest(data)
    if not data or not data.requester then return end
    local requester = NormalizeName(data.requester)
    local gid = data.gameId or gameId or "-"

    if not hostName or NormalizeName(hostName) ~= NormalizeName(OwnName()) then
        Print("Cannot accept join request: you are not the host.")
        return
    end

    if DB().lockParticipants then
        SendComm("JOINACK|" .. tostring(gid) .. "|" .. requester .. "|DENY", requester)
        Print("Denied join request from " .. requester .. ": participants are locked.")
        return
    end

    if not IsJoinEligible(requester) then
        SendComm("JOINACK|" .. tostring(gid) .. "|" .. requester .. "|DENY", requester)
        Print("Denied join request from " .. requester .. ": not eligible for the current invite/request flow.")
        return
    end

    AddParticipant(requester, "Accepted")
    SendComm("JOINACK|" .. tostring(gid) .. "|" .. requester .. "|OK", requester)
    SendPlayerJoinedComm(requester, "Accepted")
    Audit(requester .. " joined by host approval")
    Print(requester .. " joined by host approval.")

    -- Accepting a join request must not start or reset the roll timer.
    -- The countdown starts after the first valid roll, and later TURN sync keeps
    -- remote clients aligned without changing the host timer here.
    if state == "ARMED" then
        currentMax = currentMax or DB().startRoll
    elseif state == "ACTIVE" and not nextPlayer then
        nextPlayer = FindNextActivePlayerAfter(lastPlayer or requester)
    end

    SendTurnComm()
    RefreshUI()
end

local function DenyJoinRequest(data)
    if not data or not data.requester then return end
    local requester = NormalizeName(data.requester)
    local gid = data.gameId or gameId or "-"
    SendComm("JOINACK|" .. tostring(gid) .. "|" .. requester .. "|DENY", requester)
    Print("Denied join request from " .. requester .. ".")
    RefreshUI()
end

local function HandleAddonMessage(prefix, message, distribution, sender)
    if prefix ~= COMM_PREFIX then return end
    if not DB().commEnabled then return end

    sender = NormalizeName(sender)
    if sender == NormalizeName(OwnName()) then return end
    if not message or message == "" then return end

    local parts = SplitPipe(message)

    local kind = parts[1]
    if kind == "OFFER" then
        local gid, host, startRoll, minRoll, oneMeans, timeoutSeconds, betCopper, inviteScope = parts[2], NormalizeName(parts[3]), tonumber(parts[4]), tonumber(parts[5]), parts[6], tonumber(parts[7]), tonumber(parts[8]), parts[9]
        local offerState, expectedMax, offerNextPlayer, locked = parts[10], tonumber(parts[11]), NormalizeName(parts[12]), tonumber(parts[13])
        local gameMode, betMode = parts[14], parts[15]
        if not offerState or offerState == "" then offerState = "ARMED" end

        -- If the OFFER arrived through addon communication, this client has the addon
        -- and was included by the host's TARGET/PARTY/RAID invite transport.

        pendingOffer = {
            gameId = gid,
            host = host,
            startRoll = startRoll,
            minRoll = minRoll,
            oneMeans = oneMeans,
            timeoutSeconds = timeoutSeconds,
            betCopper = betCopper,
            inviteScope = inviteScope,
            state = offerState,
            expectedMax = expectedMax or startRoll,
            nextPlayer = offerNextPlayer,
            locked = locked == 1,
            gameMode = gameMode,
            betMode = betMode,
        }
        remoteHost = host
        hostName = nil
        gameId = gid
        ApplyRemoteGameSettings(startRoll, minRoll, oneMeans, timeoutSeconds, betCopper, inviteScope)
        if gameMode and gameMode ~= "" then DB().gameMode = gameMode end
        if betMode and betMode ~= "" then DB().betMode = betMode end
        if state == "IDLE" or state == "DONE" or remoteHost == host then
            state = offerState
            currentMax = expectedMax or startRoll or DB().startRoll
            nextPlayer = offerNextPlayer ~= "" and offerNextPlayer or nil
            DB().lockParticipants = locked == 1
            StopTimeout()
        end
        ShowInvitePopup(pendingOffer)
        RefreshUI()
        return
    end

    if kind == "START" and DB().acceptRemoteSync then
        local gid, host, startRoll, minRoll, oneMeans, timeoutSeconds, betCopper, inviteScope = parts[2], NormalizeName(parts[3]), tonumber(parts[4]), tonumber(parts[5]), parts[6], tonumber(parts[7]), tonumber(parts[8]), parts[9]
        if state == "IDLE" or remoteHost == host or hostName == nil then
            remoteHost = host
            hostName = nil
            gameId = gid
            ApplyRemoteGameSettings(startRoll, minRoll, oneMeans, timeoutSeconds, betCopper, inviteScope)
            state = "ARMED"
            currentMax = DB().startRoll
            resultText = nil
            SetWarning("Remote DeathRoll started by " .. tostring(host) .. ". Countdown starts after the first valid roll.")
            StopTimeout()
            RefreshUI()
        end
        return
    end

    if kind == "JOINREQ" then
        local gid, requester = parts[2], NormalizeName(parts[3] or sender)
        if hostName and NormalizeName(hostName) == NormalizeName(OwnName()) and (not gameId or gid == gameId or gid == "-") then
            pendingJoinRequest = { gameId = gid, requester = requester }
            if DB().lockParticipants then
                SendComm("JOINACK|" .. tostring(gameId or gid or "-") .. "|" .. requester .. "|DENY", requester)
                Print("Denied join request from " .. requester .. ": participants are locked.")
            elseif not IsJoinEligible(requester) then
                SendComm("JOINACK|" .. tostring(gameId or gid or "-") .. "|" .. requester .. "|DENY", requester)
                Print("Denied join request from " .. requester .. ": not eligible for the current invite/request flow.")
            elseif DB().requireJoinRequest then
                Print("Join request from " .. tostring(requester) .. ".")
                StaticPopup_Show("DEATHROLLMATE_ACCEPT_JOIN", tostring(requester), BuildScopeLabel(DB().inviteScope), pendingJoinRequest)
            else
                AddParticipant(requester, "Accepted")
                SendComm("JOINACK|" .. tostring(gameId or gid or "-") .. "|" .. requester .. "|OK", requester)
                SendPlayerJoinedComm(requester, "Accepted")
                Audit(requester .. " joined by addon request")
                Print(requester .. " joined by addon request.")
                if state == "ACTIVE" and not nextPlayer then
                    nextPlayer = FindNextActivePlayerAfter(lastPlayer or requester)
                end
                SendTurnComm()
            end
            RefreshUI()
        end
        return
    end

    if kind == "JOINACK" then
        local requester, status = NormalizeName(parts[3]), parts[4]
        if requester and NormalizeName(requester) == NormalizeName(OwnName()) then
            if status == "OK" then
                AddParticipant(OwnName(), "Accepted")
                if participants[NormalizeName(OwnName())] then
                    participants[NormalizeName(OwnName())].accepted = true
                    participants[NormalizeName(OwnName())].requested = false
                end
                if pendingOffer then
                    ApplyRemoteGameSettings(pendingOffer.startRoll, pendingOffer.minRoll, pendingOffer.oneMeans, pendingOffer.timeoutSeconds, pendingOffer.betCopper, pendingOffer.inviteScope)
                    if pendingOffer.gameMode then DB().gameMode = pendingOffer.gameMode end
                    if pendingOffer.betMode then DB().betMode = pendingOffer.betMode end
                    remoteHost = pendingOffer.host or remoteHost
                    gameId = pendingOffer.gameId or gameId
                    state = pendingOffer.state or state
                    currentMax = pendingOffer.expectedMax or currentMax or DB().startRoll
                    nextPlayer = pendingOffer.nextPlayer ~= "" and pendingOffer.nextPlayer or nextPlayer
                    DB().lockParticipants = pendingOffer.locked and true or false
                end
                -- Local accept/ack must not start a timer by itself.
                -- A TURN sync after an actual roll will start the countdown.
                StopTimeout()
                Print("Join accepted. Countdown starts after the first valid roll.")
            else
                if participants[NormalizeName(OwnName())] then
                    participants[NormalizeName(OwnName())].accepted = false
                    participants[NormalizeName(OwnName())].requested = false
                    participants[NormalizeName(OwnName())].status = "Denied"
                end
                Print("Join denied by host.")
            end
            RefreshUI()
        end
        return
    end

    if kind == "TURN" and DB().acceptRemoteSync then
        local gid, newState, maxValue, nextName, locked = parts[2], parts[3], tonumber(parts[4]), NormalizeName(parts[5]), tonumber(parts[6])
        if not gameId or gid == gameId then
            gameId = gid
            state = newState or state
            if maxValue and maxValue > 0 then currentMax = maxValue end
            nextPlayer = nextName ~= "" and nextName or nil
            DB().lockParticipants = locked == 1
            if IsJoinAccepted(OwnName()) and state == "ACTIVE" then
                StartTimeout(nextPlayer, nextPlayer and "TURN" or "JOIN")
            else
                StopTimeout()
            end
            SaveSessionSnapshot()
            RefreshUI()
        end
        return
    end

    if kind == "JOINED" and DB().acceptRemoteSync then
        local gid, playerName, statusText = parts[2], NormalizeName(parts[3]), parts[4]
        if playerName and (not gameId or gid == gameId) then
            AddParticipant(playerName, statusText or "Synced")
            Audit("Synced joined player: " .. tostring(playerName))
            SaveSessionSnapshot()
            RefreshUI()
        end
        return
    end

    if kind == "ROLL" and DB().acceptRemoteSync then
        local gid = parts[2]
        local playerName = NormalizeName(parts[3])
        local roll = tonumber(parts[4])
        local low = tonumber(parts[5])
        local high = tonumber(parts[6])
        local maxValue = tonumber(parts[7])
        local nextName = NormalizeName(parts[8])
        local newState = parts[9]
        local locked = tonumber(parts[10])
        if playerName and roll and low and high and (not gameId or gid == gameId) then
            gameId = gid
            local p = AddParticipant(playerName, "Synced")
            p.rolls = (p.rolls or 0) + 1
            p.last = roll
            p.status = "Active"
            p.accepted = true
            p.requested = false
            lastPlayer = playerName
            lastRoll = roll
            lastRange = "(" .. tostring(low) .. "-" .. tostring(high) .. ")"
            currentMax = maxValue or roll
            state = newState or "ACTIVE"
            nextPlayer = nextName ~= "" and nextName or nil
            DB().lockParticipants = locked == 1
            AddHistory(playerName, roll, low, high, "Host accepted")
            Audit("Host accepted roll from " .. tostring(playerName) .. ": " .. tostring(roll))
            if IsJoinAccepted(OwnName()) and state == "ACTIVE" then
                StartTimeout(nextPlayer, nextPlayer and "TURN" or "JOIN")
            else
                StopTimeout()
            end
            SaveSessionSnapshot()
            RefreshUI()
        end
        return
    end

    if kind == "REJECT" and DB().acceptRemoteSync then
        local gid = parts[2]
        local playerName = NormalizeName(parts[3])
        local reason = parts[4] or "rejected"
        local roll = parts[5]
        local low = parts[6]
        local high = parts[7]
        if playerName and (not gameId or gid == gameId) then
            local text = "Rejected roll from " .. tostring(playerName) .. ": " .. tostring(reason) .. "."
            warningText = text
            AddHistory(playerName, roll or "-", low or "-", high or "-", "Rejected: " .. tostring(reason))
            Audit(text)
            RefreshUI()
        end
        return
    end

    if kind == "HELLO" then
        versionPeers[sender] = parts[3] or "unknown"
        SendComm("VERSION|" .. tostring(parts[2] or gameId or "-") .. "|" .. VERSION, sender)
        RefreshUI()
        return
    end

    if kind == "VERSION" then
        versionPeers[sender] = parts[3] or "unknown"
        RefreshUI()
        return
    end

    if kind == "RESULT" then
        local gid, text = parts[2], parts[3]
        if text and (not gameId or gid == gameId) then
            resultText = text
            state = "DONE"
            StopTimeout()
            Print("Remote result: " .. text)
            RefreshUI()
        end
        return
    end
end

StaticPopupDialogs["DEATHROLLMATE_RESTORE"] = {
    text = "Previous DeathRollMate session found. Restore it?",
    button1 = "Restore",
    button2 = "Discard",
    OnAccept = function() RestoreSessionSnapshot() end,
    OnCancel = function() DiscardSessionSnapshot() end,
    timeout = 0,
    whileDead = true,
    hideOnEscape = true,
}

StaticPopupDialogs["DEATHROLLMATE_JOIN"] = {
    text = "DeathRoll invite from %s.\n%s\nAccept invite and request entry?",
    button1 = "Accept",
    button2 = "Ignore",
    OnAccept = function(self, data)
        if data then pendingOffer = data end
        if not pendingOffer then
            Print("No pending invite is available. Ask the host to send Invite again.")
            return
        end
        SendJoinRequest()
    end,
    timeout = 0,
    whileDead = true,
    hideOnEscape = true,
}

StaticPopupDialogs["DEATHROLLMATE_ACCEPT_JOIN"] = {
    text = "Join request from %s. Invite scope: %s. Accept?",
    button1 = "Accept",
    button2 = "Ignore",
    OnAccept = function(self, data)
        AcceptJoinRequest(data)
    end,
    OnCancel = function(self, data)
        DenyJoinRequest(data)
    end,
    timeout = 0,
    whileDead = true,
    hideOnEscape = true,
}

local function CreateLabel(parent, text, x, y, width)
    local label = parent:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    label:SetPoint("TOPLEFT", parent, "TOPLEFT", x, y)
    label:SetWidth(width or 320)
    label:SetJustifyH("LEFT")
    label:SetText(text or "")
    SetFontColor(label, STYLE.text)
    return label
end

local function CreateButton(parent, text, x, y, width, height, onClick)
    local button = CreateFrame("Button", nil, parent)
    button:SetWidth(width or 80)
    button:SetHeight(height or 22)
    button:SetPoint("TOPLEFT", parent, "TOPLEFT", x, y)
    ApplyBackdrop(button, "panel")

    local label = button:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    label:SetPoint("CENTER", button, "CENTER", 0, 0)
    SetFontColor(label, STYLE.text)
    button:SetFontString(label)
    button:SetText(text)

    button:SetScript("OnEnter", function(self)
        ApplyAccentBorder(self)
        if self:GetFontString() then SetFontColor(self:GetFontString(), STYLE.accent) end
    end)
    button:SetScript("OnLeave", function(self)
        self:SetBackdropBorderColor(STYLE.border[1], STYLE.border[2], STYLE.border[3], STYLE.border[4])
        if self:GetFontString() then SetFontColor(self:GetFontString(), STYLE.text) end
    end)
    button:SetScript("OnMouseDown", function(self)
        self:SetBackdropColor(0.12, 0.10, 0.07, 0.95)
    end)
    button:SetScript("OnMouseUp", function(self)
        local bg = STYLE.bg2
        self:SetBackdropColor(bg[1], bg[2], bg[3], bg[4])
    end)
    button:SetScript("OnClick", function()
        if onClick then onClick() end
    end)
    return button
end

local function CreateEditBox(parent, x, y, width, maxLetters)
    local editBox = CreateFrame("EditBox", nil, parent)
    editBox:SetWidth(width or 80)
    editBox:SetHeight(22)
    editBox:SetPoint("TOPLEFT", parent, "TOPLEFT", x, y)
    editBox:SetAutoFocus(false)
    editBox:SetNumeric(true)
    editBox:SetMaxLetters(maxLetters or 8)
    editBox:SetJustifyH("CENTER")
    if GameFontHighlightSmall then editBox:SetFontObject(GameFontHighlightSmall) end
    editBox:SetTextColor(STYLE.text[1], STYLE.text[2], STYLE.text[3], STYLE.text[4])
    editBox:SetTextInsets(4, 4, 0, 0)
    ApplyBackdrop(editBox, "panel")
    editBox:SetScript("OnEditFocusGained", function(self)
        ApplyAccentBorder(self)
    end)
    editBox:SetScript("OnEnterPressed", function(self)
        self:ClearFocus()
        ApplySettingsFromUI()
        RefreshUI()
    end)
    editBox:SetScript("OnEscapePressed", function(self)
        self:ClearFocus()
        RefreshUI()
    end)
    editBox:SetScript("OnEditFocusLost", function(self)
        self:SetBackdropBorderColor(STYLE.border[1], STYLE.border[2], STYLE.border[3], STYLE.border[4])
        ApplySettingsFromUI()
        RefreshUI()
    end)
    return editBox
end

local function CreateCheck(parent, text, x, y, onClick)
    local check = CreateFrame("CheckButton", nil, parent, "OptionsCheckButtonTemplate")
    check:SetPoint("TOPLEFT", parent, "TOPLEFT", x, y)
    check:SetWidth(22)
    check:SetHeight(22)

    local label = parent:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    label:SetPoint("LEFT", check, "RIGHT", 2, 0)
    label:SetText(text)
    SetFontColor(label, STYLE.text)
    check.label = label

    check:SetScript("OnClick", function()
        ApplySettingsFromUI()
        if onClick then onClick(check) end
        RefreshUI()
    end)

    return check
end

local function CreateParticipantsScroll(parent, x, y, width, height)
    local scroll = CreateFrame("ScrollFrame", "DeathRollMateParticipantsScrollFrame", parent, "UIPanelScrollFrameTemplate")
    scroll:SetPoint("TOPLEFT", parent, "TOPLEFT", x, y)
    scroll:SetWidth(width)
    scroll:SetHeight(height)
    ApplyBackdrop(scroll, "panel")

    local content = CreateFrame("Frame", nil, scroll)
    content:SetWidth(width - 32)
    content:SetHeight(height)
    scroll:SetScrollChild(content)

    ui.participantScroll = scroll
    ui.participantContent = content
    ui.participantLines = {}

    for i = 1, 50 do
        local line = content:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
        line:SetPoint("TOPLEFT", content, "TOPLEFT", 6, -6 - ((i - 1) * 16))
        line:SetWidth(width - 42)
        line:SetJustifyH("LEFT")
        SetFontColor(line, STYLE.text)
        SetFontColor(line, STYLE.text)
        line:SetText("")
        line:Hide()
        ui.participantLines[i] = line
    end

    return scroll
end

local function CreateHistoryScroll(parent, x, y, width, height)
    local scroll = CreateFrame("ScrollFrame", "DeathRollMateHistoryScrollFrame", parent, "UIPanelScrollFrameTemplate")
    scroll:SetPoint("TOPLEFT", parent, "TOPLEFT", x, y)
    scroll:SetWidth(width)
    scroll:SetHeight(height)
    ApplyBackdrop(scroll, "panel")

    local content = CreateFrame("Frame", nil, scroll)
    content:SetWidth(width - 32)
    content:SetHeight(height)
    scroll:SetScrollChild(content)

    ui.historyScroll = scroll
    ui.historyContent = content
    ui.historyLines = {}

    for i = 1, 50 do
        local line = content:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
        line:SetPoint("TOPLEFT", content, "TOPLEFT", 6, -6 - ((i - 1) * 16))
        line:SetWidth(width - 42)
        line:SetJustifyH("LEFT")
        line:SetText("")
        line:Hide()
        ui.historyLines[i] = line
    end

    return scroll
end


local function RefreshSettlementPanel()
    if not settlementUi.frame then return end
    for i = 1, #settlementUi.lines do
        local line = settlementUi.lines[i]
        local check = settlementUi.checks[i]
        local e = settlementEntries[i]
        if e then
            line:SetText(tostring(e.from) .. " -> " .. tostring(e.to) .. ": " .. FormatMoney(e.amount) .. (e.reason and ("  [" .. e.reason .. "]") or ""))
            check:SetChecked(e.paid and true or false)
            line:Show(); check:Show()
        else
            line:SetText(""); line:Hide(); check:Hide()
        end
    end
end

ShowSettlementPanel = function()
    if #settlementEntries == 0 then
        Print("No settlement entries to show.")
        return
    end

    if not settlementUi.frame then
        local f = CreateFrame("Frame", "DeathRollMateSettlementFrame", UIParent)
        settlementUi.frame = f
        f:SetWidth(470)
        f:SetHeight(260)
        f:SetPoint("CENTER", UIParent, "CENTER", 0, -90)
        f:SetFrameStrata("DIALOG")
        f:SetMovable(true)
        f:EnableMouse(true)
        f:RegisterForDrag("LeftButton")
        f:SetClampedToScreen(true)
        ApplyBackdrop(f, "main")
        f:SetScript("OnDragStart", function(self) if not DB().lockFrame then self:StartMoving() end end)
        f:SetScript("OnDragStop", function(self) self:StopMovingOrSizing() end)

        local close = CreateFrame("Button", nil, f, "UIPanelCloseButton")
        close:SetPoint("TOPRIGHT", f, "TOPRIGHT", -5, -5)
        close:SetScript("OnClick", function() f:Hide() end)

        local title = CreateLabel(f, "DeathRoll Settlement", 18, -16, 280)
        SetFontColor(title, STYLE.accent)
        settlementUi.lines = {}
        settlementUi.checks = {}
        for i = 1, 10 do
            local check = CreateFrame("CheckButton", nil, f, "OptionsCheckButtonTemplate")
            check:SetPoint("TOPLEFT", f, "TOPLEFT", 18, -44 - ((i - 1) * 18))
            check:SetScript("OnClick", function(self)
                if settlementEntries[i] then settlementEntries[i].paid = self:GetChecked() and true or false end
            end)
            local line = CreateLabel(f, "", 44, -43 - ((i - 1) * 18), 390)
            settlementUi.checks[i] = check
            settlementUi.lines[i] = line
        end
        CreateButton(f, "Announce", 18, -224, 90, 22, function()
            if resultText then SafeSendChat("[DeathRoll] " .. resultText) else SafeSendChat("[DeathRoll] " .. BuildSettlementEntryText("Settlement")) end
        end)
        CreateButton(f, "Unpaid", 116, -224, 80, 22, function()
            local lines = {}
            for i = 1, #settlementEntries do
                local e = settlementEntries[i]
                if not e.paid then table.insert(lines, e.from .. " -> " .. e.to .. ": " .. FormatMoney(e.amount)) end
            end
            if #lines == 0 then Print("All settlement entries are marked paid.") else Print("Unpaid: " .. table.concat(lines, "; ")) end
        end)
        CreateButton(f, "Close", 374, -224, 72, 22, function() f:Hide() end)
    end

    RefreshSettlementPanel()
    settlementUi.frame:Show()
end

local function CreateMinimapButton()
    if ui.minimapButton or not Minimap then return end

    local b = CreateFrame("Button", "DeathRollMateMinimapButton", Minimap)
    ui.minimapButton = b
    b:SetWidth(32)
    b:SetHeight(32)
    b:SetPoint("TOPLEFT", Minimap, "TOPLEFT", 4, -4)
    b:SetFrameStrata("MEDIUM")
    b:SetFrameLevel((Minimap:GetFrameLevel() or 0) + 8)
    b:RegisterForClicks("LeftButtonUp", "RightButtonUp")

    -- Draw the icon as explicit child textures instead of relying on
    -- SetNormalTexture.  Some 3.3.5 clients silently fail custom addon
    -- TGA normal textures; keeping a built-in fallback underneath ensures
    -- the minimap button is never blank.
    local fallback = b:CreateTexture(nil, "BACKGROUND")
    fallback:SetPoint("CENTER", b, "CENTER", 0, 0)
    fallback:SetWidth(30)
    fallback:SetHeight(30)
    fallback:SetTexture(MINIMAP_FALLBACK_ICON)
    fallback:SetTexCoord(0.08, 0.92, 0.08, 0.92)
    b.fallbackIcon = fallback

    local icon = b:CreateTexture(nil, "ARTWORK")
    icon:SetPoint("CENTER", b, "CENTER", 0, 0)
    icon:SetWidth(30)
    icon:SetHeight(30)
    icon:SetTexture(MINIMAP_ICON)
    icon:SetTexCoord(0.06, 0.94, 0.06, 0.94)
    b.icon = icon

    local highlight = b:CreateTexture(nil, "HIGHLIGHT")
    highlight:SetTexture("Interface\\Minimap\\UI-Minimap-ZoomButton-Highlight")
    highlight:SetPoint("CENTER", b, "CENTER", 0, 0)
    highlight:SetWidth(48)
    highlight:SetHeight(48)
    highlight:SetBlendMode("ADD")
    b:SetHighlightTexture(highlight)

    b:SetScript("OnEnter", function(self)
        GameTooltip:SetOwner(self, "ANCHOR_LEFT")
        GameTooltip:AddLine("DeathRollMate " .. VERSION)
        GameTooltip:AddLine("Left click: game", 0.88, 0.88, 0.84)
        GameTooltip:AddLine("Right click: config", 0.88, 0.88, 0.84)
        GameTooltip:Show()
    end)
    b:SetScript("OnLeave", function()
        GameTooltip:Hide()
    end)
    b:SetScript("OnClick", function(self, button)
        if button == "RightButton" then
            if ToggleConfig then ToggleConfig() end
        else
            DR:Toggle()
        end
    end)
end

UpdateMinimapButton = function()
    if not ui.minimapButton then CreateMinimapButton() end
    if ui.minimapButton then
        if DB().minimapEnabled then ui.minimapButton:Show() else ui.minimapButton:Hide() end
    end
end

local CreateUI

ToggleConfig = function()
    CreateUI()
    if ui.configFrame:IsShown() then
        ApplySettingsFromUI()
        ui.configFrame:Hide()
    else
        if ui.frame and ui.frame:IsShown() then
            ui.frame:Hide()
            DB().visible = false
        end
        ui.configFrame:Show()
        RefreshUI()
    end
end

local function CreateConfigPanel(parent)
    if ui.configFrame then return end

    local db = DB()
    local config = CreateFrame("Frame", "DeathRollMateConfigFrame", UIParent)
    ui.configFrame = config

    config:SetWidth(460)
    config:SetHeight(560)
    config:SetPoint("TOPLEFT", parent, "TOPRIGHT", 8, 0)
    config:SetFrameStrata("DIALOG")
    config:SetMovable(true)
    config:EnableMouse(true)
    config:RegisterForDrag("LeftButton")
    config:SetClampedToScreen(true)
    ApplyBackdrop(config, "main")
    config:SetScript("OnDragStart", function(self)
        if not DB().lockFrame then self:StartMoving() end
    end)
    config:SetScript("OnDragStop", function(self)
        self:StopMovingOrSizing()
    end)

    local close = CreateFrame("Button", nil, config, "UIPanelCloseButton")
    close:SetPoint("TOPRIGHT", config, "TOPRIGHT", -5, -5)
    close:SetScript("OnClick", function()
        ApplySettingsFromUI()
        config:Hide()
    end)

    local configTitle = CreateLabel(config, "DeathRollMate Config", 18, -16, 260)
    SetFontColor(configTitle, STYLE.accent)

    CreateSectionTitle(config, "Game presets", 18, -48, 150)
    ui.modeButton = CreateButton(config, "Mode: Reverse", 18, -76, 126, 22, ToggleGameMode)
    ui.betModeButton = CreateButton(config, "Bet mode: Pot", 154, -76, 136, 22, ToggleBetMode)
    ui.ruleButton = CreateButton(config, "1 wins", 300, -76, 70, 22, ToggleRule)

    CreateSectionTitle(config, "Roll and bet", 18, -114, 150)
    CreateLabel(config, "Starting max:", 18, -142, 90)
    ui.startBox = CreateEditBox(config, 110, -139, 82, 8)
    CreateLabel(config, "Minimum:", 210, -142, 60)
    ui.minBox = CreateEditBox(config, 275, -139, 54, 5)

    CreateLabel(config, "Timeout:", 18, -174, 60)
    ui.timeoutBox = CreateEditBox(config, 78, -171, 54, 4)
    CreateLabel(config, "sec", 138, -174, 30)

    CreateLabel(config, "Bet:", 185, -174, 34)
    ui.betGoldBox = CreateEditBox(config, 219, -171, 50, 6)
    CreateLabel(config, "g", 273, -174, 14)
    ui.betSilverBox = CreateEditBox(config, 289, -171, 38, 2)
    CreateLabel(config, "s", 331, -174, 14)
    ui.betCopperBox = CreateEditBox(config, 347, -171, 38, 2)
    CreateLabel(config, "c", 389, -174, 14)

    CreateSectionTitle(config, "Communication and scope", 18, -212, 220)
    ui.reportButton = CreateButton(config, "Report: auto", 18, -240, 120, 22, ToggleReportChannel)
    ui.watchButton = CreateButton(config, "Watch: visible", 148, -240, 126, 22, ToggleWatchScope)
    ui.inviteButton = CreateButton(config, "Invite: party", 284, -240, 126, 22, ToggleInviteScope)

    CreateSectionTitle(config, "Automation", 18, -280, 150)
    ui.autoJoin = CreateCheck(config, "Auto-join valid rollers", 18, -304)
    ui.validateRange = CreateCheck(config, "Validate roll range", 18, -328)
    ui.autoReportResult = CreateCheck(config, "Report result", 18, -352)
    ui.commEnabled = CreateCheck(config, "Addon comm", 18, -376)
    ui.requireJoinRequest = CreateCheck(config, "Approve join requests", 18, -400)
    ui.soundEnabled = CreateCheck(config, "Sound warnings", 18, -424)

    ui.lockPlayers = CreateCheck(config, "Lock participants", 230, -304)
    ui.showCountdown = CreateCheck(config, "Countdown popup", 230, -328)
    ui.lockFrame = CreateCheck(config, "Lock frames", 230, -352)
    ui.timeoutEnabled = CreateCheck(config, "Roll timeout", 230, -376)
    ui.acceptRemoteSync = CreateCheck(config, "Accept remote sync", 230, -400)
    ui.minimapEnabled = CreateCheck(config, "Minimap button", 230, -424)

    CreateSectionTitle(config, "Diagnostics", 18, -462, 410)
    ui.versionSummary = CreateLabel(config, "Addon peers: 0", 18, -484, 160)
    CreateButton(config, "Check versions", 190, -480, 110, 22, SendVersionCheck)
    CreateButton(config, "Settlement", 310, -480, 90, 22, function() if ShowSettlementPanel then ShowSettlementPanel() else Print("No settlement panel available yet.") end end)

    local note1 = CreateLabel(config, "Invite uses addon comm only: target whisper, party, or raid. Players without the addon can still join by valid manual /roll.", 18, -518, 410)
    note1:SetTextColor(0.85, 0.85, 0.85)
    config:Hide()
end

CreateUI = function()
    if ui.frame then return end

    local db = DB()
    local frame = CreateFrame("Frame", "DeathRollMateMainFrame", UIParent)
    ui.frame = frame

    frame:SetWidth(480)
    frame:SetHeight(500)
    frame:SetPoint(db.point or "CENTER", UIParent, db.relativePoint or "CENTER", db.x or 0, db.y or 0)
    frame:SetScale(db.scale or 1)
    frame:SetMovable(true)
    frame:EnableMouse(true)
    frame:RegisterForDrag("LeftButton")
    frame:SetClampedToScreen(true)
    ApplyBackdrop(frame, "main")
    frame:SetScript("OnDragStart", function(self)
        if not DB().lockFrame then self:StartMoving() end
    end)
    frame:SetScript("OnDragStop", function(self)
        self:StopMovingOrSizing()
        SavePosition()
    end)

    local close = CreateFrame("Button", nil, frame, "UIPanelCloseButton")
    close:SetPoint("TOPRIGHT", frame, "TOPRIGHT", -5, -5)
    close:SetScript("OnClick", function()
        DB().visible = false
        if ui.configFrame then ui.configFrame:Hide() end
        frame:Hide()
    end)

    ui.title = CreateLabel(frame, "DeathRollMate", 18, -16, 350)
    SetFontColor(ui.title, STYLE.accent)
    ui.status = CreateLabel(frame, "Idle", 18, -45, 440)

    ui.expected = frame:CreateFontString(nil, "OVERLAY", "GameFontNormalLarge")
    ui.expected:SetPoint("TOPLEFT", frame, "TOPLEFT", 18, -66)
    ui.expected:SetWidth(440)
    ui.expected:SetJustifyH("LEFT")
    ui.expected:SetText("Roll: -")
    SetFontColor(ui.expected, STYLE.accent)

    ui.next = CreateLabel(frame, "Next: -", 18, -92, 440)
    ui.timeout = CreateLabel(frame, "Roll timeout: 10s", 18, -111, 440)
    ui.bet = CreateLabel(frame, "min roll wins    Bet: off", 18, -130, 440)
    ui.last = CreateLabel(frame, "Last: -", 18, -149, 440)
    ui.result = CreateLabel(frame, "Ready.", 18, -170, 440)

    CreateButton(frame, "New Game", 18, -202, 82, 22, NewGame)
    CreateButton(frame, "Roll", 106, -202, 62, 22, RollNow)
    CreateButton(frame, "Invite", 174, -202, 62, 22, Invite)
    ui.gameJoinButton = CreateButton(frame, "Join", 242, -202, 62, 22, SendJoinRequest)
    CreateButton(frame, "Announce", 310, -202, 82, 22, Announce)
    CreateButton(frame, "Reset", 398, -202, 62, 22, ResetAll)

    CreateButton(frame, "Config", 18, -232, 72, 22, ToggleConfig)
    CreateButton(frame, "Clear", 96, -232, 62, 22, function()
        ClearTable(participants)
        ClearTable(participantOrder)
        nextPlayer = nil
        RefreshUI()
    end)

    CreateSectionTitle(frame, "Participants", 18, -270, 350)
    CreateParticipantsScroll(frame, 18, -290, 440, 86)

    CreateSectionTitle(frame, "History", 18, -392, 350)
    CreateHistoryScroll(frame, 18, -412, 440, 58)

    CreateConfigPanel(frame)

    frame:Hide()
    RefreshUI()
end

function DR:Toggle()
    CreateUI()
    if ui.frame:IsShown() then
        ui.frame:Hide()
        if ui.configFrame then ui.configFrame:Hide() end
        DB().visible = false
    else
        if ui.configFrame and ui.configFrame:IsShown() then
            ApplySettingsFromUI()
            ui.configFrame:Hide()
        end
        ui.frame:Show()
        DB().visible = true
        RefreshUI()
    end
end

function DR:ShowUI()
    CreateUI()
    if ui.configFrame and ui.configFrame:IsShown() then
        ApplySettingsFromUI()
        ui.configFrame:Hide()
    end
    ui.frame:Show()
    DB().visible = true
    RefreshUI()
end

DR:RegisterEvent("ADDON_LOADED")
DR:RegisterEvent("CHAT_MSG_SYSTEM")
DR:RegisterEvent("CHAT_MSG_ADDON")
DR:RegisterEvent("PARTY_MEMBERS_CHANGED")
DR:RegisterEvent("RAID_ROSTER_UPDATE")

DR:SetScript("OnUpdate", function(self, elapsed)
    if timeoutDeadline and GetTime() >= timeoutDeadline then
        timeoutUiAccumulator = 0
        HandleTimeoutExpired()
    elseif timeoutDeadline then
        timeoutUiAccumulator = timeoutUiAccumulator + (elapsed or 0)
        if timeoutUiAccumulator >= 0.10 then
            timeoutUiAccumulator = 0
            RefreshUI()
        end
    end
end)

DR:SetScript("OnEvent", function(self, event, ...)
    if event == "ADDON_LOADED" then
        local loadedName = ... or arg1
        if loadedName == ADDON_NAME then
            DB()
            if RegisterAddonMessagePrefix then
                RegisterAddonMessagePrefix(COMM_PREFIX)
            end
            versionPeers[NormalizeName(OwnName())] = VERSION
            if UpdateMinimapButton then UpdateMinimapButton() end
            if DeathRollMateDB and DeathRollMateDB.lastSession and DeathRollMateDB.lastSession.state and DeathRollMateDB.lastSession.state ~= "IDLE" and not sessionRestorePromptShown then
                sessionRestorePromptShown = true
                if StaticPopup_Show then StaticPopup_Show("DEATHROLLMATE_RESTORE") end
                Print("previous session found. Use /dr restore or /dr discard.")
            end
            Print("loaded. Use /dr or /deathroll.")
        end
        return
    end

    if event == "CHAT_MSG_SYSTEM" then
        local message = ... or arg1
        local player, roll, low, high = ParseRollMessage(message)
        if player and roll and low and high then
            HandleRoll(player, roll, low, high)
        end
        return
    end

    if event == "CHAT_MSG_ADDON" then
        local prefix, message, distribution, sender = ...
        if not prefix then
            prefix, message, distribution, sender = arg1, arg2, arg3, arg4
        end
        HandleAddonMessage(prefix, message, distribution, sender)
        return
    end

    if event == "PARTY_MEMBERS_CHANGED" or event == "RAID_ROSTER_UPDATE" then
        if ui.frame then RefreshUI() end
        return
    end
end)

SLASH_DEATHROLLMATE1 = "/dr"
SLASH_DEATHROLLMATE2 = "/deathroll"
SlashCmdList["DEATHROLLMATE"] = function(message)
    message = string.lower(message or "")

    if message == "" or message == "show" or message == "toggle" then
        DR:Toggle()
        return
    end

    if message == "config" or message == "settings" or message == "options" then
        ToggleConfig()
        return
    end

    if string.find(message, "^new") then
        local amount = string.match(message, "^new%s+(%d+)$")
        if amount then DB().startRoll = tonumber(amount) end
        DR:ShowUI()
        NewGame()
        return
    end

    if message == "roll" then
        DR:ShowUI()
        RollNow()
        return
    end

    if message == "invite" then
        DR:ShowUI()
        Invite()
        return
    end

    if message == "join" then
        DR:ShowUI()
        SendJoinRequest()
        return
    end

    if message == "reset" then
        DR:ShowUI()
        ResetAll()
        return
    end

    if message == "announce" then
        Announce()
        return
    end

    local reportChannel = string.match(message, "^report%s+(%a+)$")
    if reportChannel then
        reportChannel = string.upper(reportChannel)
        if reportChannel == "ME" then reportChannel = "SELF" end
        if reportChannel == "AUTO" or reportChannel == "SAY" or reportChannel == "PARTY" or reportChannel == "RAID" or reportChannel == "SELF" then
            DB().reportChannel = reportChannel
            DR:ShowUI()
            RefreshUI()
            Print("Report channel: " .. BuildReportLabel())
        else
            Print("Valid report channels: auto, say, party, raid, me")
        end
        return
    end

    local watchScope = string.match(message, "^watch%s+(%a+)$")
    if watchScope then
        watchScope = string.upper(watchScope)
        if watchScope == "VISIBLE" or watchScope == "ALL" then watchScope = "SAY" end
        if watchScope == "SAY" or watchScope == "PARTY" or watchScope == "RAID" or watchScope == "NEARBY" then
            DB().watchScope = watchScope
            DR:ShowUI()
            RefreshUI()
            Print("Watch scope: " .. BuildScopeLabel(DB().watchScope))
        else
            Print("Valid watch scopes: visible, party, raid, nearby")
        end
        return
    end

    local inviteScope = string.match(message, "^scope%s+(%a+)$") or string.match(message, "^invite%s+scope%s+(%a+)$") or string.match(message, "^invite%s+(target)$") or string.match(message, "^invite%s+(party)$") or string.match(message, "^invite%s+(raid)$")
    if inviteScope then
        inviteScope = string.upper(inviteScope)
        if inviteScope == "TARGET" or inviteScope == "PARTY" or inviteScope == "RAID" then
            DB().inviteScope = inviteScope
            DR:ShowUI()
            RefreshUI()
            Print("Invite scope: " .. BuildScopeLabel(DB().inviteScope))
        else
            Print("Valid invite scopes: target, party, raid")
        end
        return
    end

    local timeoutValue = string.match(message, "^timeout%s+(%d+)$")
    if timeoutValue then
        DB().timeoutSeconds = tonumber(timeoutValue) or 10
        DB().timeoutEnabled = DB().timeoutSeconds > 0
        if not DB().timeoutEnabled then StopTimeout() end
        DR:ShowUI()
        RefreshUI()
        Print("Roll timeout: " .. tostring(DB().timeoutSeconds) .. " seconds")
        return
    end

    if message == "timeout off" then
        DB().timeoutEnabled = false
        StopTimeout()
        DR:ShowUI()
        RefreshUI()
        Print("Roll timeout disabled.")
        return
    end

    if message == "timeout on" then
        DB().timeoutEnabled = true
        if state == "ACTIVE" then StartTimeout(nextPlayer, nextPlayer and "TURN" or "JOIN") end
        DR:ShowUI()
        RefreshUI()
        Print("Roll timeout enabled: " .. tostring(DB().timeoutSeconds or 10) .. " seconds")
        return
    end

    if message == "countdown reset" then
        local db = DB()
        db.countdownPoint = "CENTER"
        db.countdownRelativePoint = "CENTER"
        db.countdownX = 0
        db.countdownY = 170
        if countdown.frame then
            countdown.frame:ClearAllPoints()
            countdown.frame:SetPoint("CENTER", UIParent, "CENTER", 0, 170)
        end
        RefreshUI()
        Print("Countdown popup position reset.")
        return
    end

    if message == "countdown off" then
        DB().showCountdown = false
        HideCountdown()
        DR:ShowUI()
        RefreshUI()
        Print("Countdown popup disabled.")
        return
    end

    if message == "countdown on" then
        DB().showCountdown = true
        DR:ShowUI()
        RefreshUI()
        Print("Countdown popup enabled.")
        return
    end

    if message == "comm on" then
        DB().commEnabled = true
        DR:ShowUI()
        RefreshUI()
        Print("Addon communication enabled.")
        return
    end

    if message == "comm off" then
        DB().commEnabled = false
        DR:ShowUI()
        RefreshUI()
        Print("Addon communication disabled.")
        return
    end

    if message == "requirejoin on" or message == "joinreq on" then
        DB().requireJoinRequest = true
        DR:ShowUI()
        RefreshUI()
        Print("Host approval popup enabled for addon join requests.")
        return
    end

    if message == "requirejoin off" or message == "joinreq off" then
        DB().requireJoinRequest = false
        DR:ShowUI()
        RefreshUI()
        Print("Host approval popup disabled; addon join requests are accepted automatically. Valid rollers still auto-join.")
        return
    end

    local betText = string.match(message, "^bet%s+(.+)$")
    if betText then
        local gold, silver, copper = string.match(betText, "^(%d+)%s+(%d+)%s+(%d+)$")
        if not gold then
            gold = string.match(betText, "(%d+)%s*g")
            silver = string.match(betText, "(%d+)%s*s")
            copper = string.match(betText, "(%d+)%s*c")
            if not gold and not silver and not copper then gold = string.match(betText, "^(%d+)$") end
        end
        DB().betGold = tonumber(gold) or 0
        DB().betSilver = tonumber(silver) or 0
        DB().betCopper = tonumber(copper) or 0
        DB()
        DR:ShowUI()
        RefreshUI()
        Print(BuildBetLabel())
        return
    end

    if message == "lock" then
        DB().lockParticipants = not DB().lockParticipants
        if DB().lockParticipants and state == "ACTIVE" then
            nextPlayer = FindNextActivePlayerAfter(lastPlayer or participantOrder[1])
            StartTimeout(nextPlayer, "TURN")
        elseif not DB().lockParticipants and state == "ACTIVE" then
            nextPlayer = nil
            StartTimeout(nil, "JOIN")
        end
        DR:ShowUI()
        RefreshUI()
        Print("Participants locked: " .. tostring(DB().lockParticipants))
        return
    end

    local modeValue = string.match(message, "^mode%s+(%a+)$")
    if modeValue then
        modeValue = string.upper(modeValue)
        if modeValue == "REVERSE" or modeValue == "CLASSIC" or modeValue == "ELIMINATION" or modeValue == "FREE" then
            DB().gameMode = modeValue
            ApplyGameModePreset(modeValue)
            DR:ShowUI()
            RefreshUI()
            Print("Game mode: " .. BuildGameModeLabel())
        else
            Print("Valid game modes: reverse, classic, elimination, free")
        end
        return
    end

    local betModeValue = string.match(message, "^betmode%s+(%a+)$")
    if betModeValue then
        betModeValue = string.upper(betModeValue)
        if betModeValue == "POT" or betModeValue == "WINNER" or betModeValue == "WINNER_TAKES" or betModeValue == "LOSER" or betModeValue == "LOSER_PAYS" then
            if betModeValue == "WINNER" then betModeValue = "WINNER_TAKES" end
            if betModeValue == "LOSER" then betModeValue = "LOSER_PAYS" end
            DB().betMode = betModeValue
            DR:ShowUI()
            RefreshUI()
            Print("Bet mode: " .. BuildBetModeLabel())
        else
            Print("Valid bet modes: pot, winner, loser")
        end
        return
    end

    if message == "minimap" or message == "minimap on" then
        DB().minimapEnabled = true
        if UpdateMinimapButton then UpdateMinimapButton() end
        Print("Minimap button enabled.")
        return
    end

    if message == "minimap off" then
        DB().minimapEnabled = false
        if UpdateMinimapButton then UpdateMinimapButton() end
        Print("Minimap button disabled.")
        return
    end

    if message == "versions" or message == "version" then
        SendVersionCheck()
        PrintVersionSummary()
        return
    end

    if message == "restore" then
        DR:ShowUI()
        RestoreSessionSnapshot()
        return
    end

    if message == "discard" then
        DiscardSessionSnapshot()
        return
    end

    if message == "settlement" or message == "pay" then
        if ShowSettlementPanel then ShowSettlementPanel() end
        return
    end

    if message == "audit" then
        Print("Audit log:")
        local startIndex = math.max(1, #auditLog - 9)
        for i = startIndex, #auditLog do Print(auditLog[i]) end
        return
    end

    local addName = string.match(message, "^add%s+(.+)$")
    if addName then
        AddParticipant(addName, "Admin-added")
        SendPlayerJoinedComm(addName, "Admin-added")
        Audit("Admin added player: " .. tostring(addName))
        DR:ShowUI(); RefreshUI(); SaveSessionSnapshot()
        return
    end

    local removeName = string.match(message, "^remove%s+(.+)$")
    if removeName then
        removeName = NormalizeName(removeName)
        participants[removeName] = nil
        for i = #participantOrder, 1, -1 do if NormalizeName(participantOrder[i]) == removeName then table.remove(participantOrder, i) end end
        Audit("Admin removed player: " .. tostring(removeName))
        DR:ShowUI(); RefreshUI(); SaveSessionSnapshot()
        return
    end

    local outName = string.match(message, "^out%s+(.+)$")
    if outName then
        EliminatePlayer(outName, "Admin eliminated")
        Audit("Admin eliminated player: " .. tostring(outName))
        DR:ShowUI(); RefreshUI(); SaveSessionSnapshot()
        return
    end

    local nextName = string.match(message, "^next%s+(.+)$")
    if nextName then
        nextPlayer = NormalizeName(nextName)
        Audit("Admin set next player: " .. tostring(nextPlayer))
        if state == "ACTIVE" then StartTimeout(nextPlayer, "TURN"); SendTurnComm() end
        DR:ShowUI(); RefreshUI(); SaveSessionSnapshot()
        return
    end

    local correctMax = string.match(message, "^correct%s+(%d+)$")
    if correctMax then
        currentMax = tonumber(correctMax)
        state = "ACTIVE"
        Audit("Admin corrected current max to " .. tostring(currentMax))
        if state == "ACTIVE" then SendTurnComm() end
        DR:ShowUI(); RefreshUI(); SaveSessionSnapshot()
        return
    end

    local testPlayers = string.match(message, "^test%s+players%s+(%d+)$")
    if testPlayers then
        local n = math.min(10, tonumber(testPlayers) or 0)
        if state == "IDLE" or state == "DONE" then NewGame() end
        for i = 1, n do AddParticipant("Test" .. tostring(i), "Test") end
        Audit("Test added " .. tostring(n) .. " players")
        DR:ShowUI(); RefreshUI(); SaveSessionSnapshot()
        return
    end

    local testPlayer, testRoll, testMax = string.match(message, "^test%s+roll%s+(%S+)%s+(%d+)%s+(%d+)$")
    if testPlayer and testRoll and testMax then
        if state == "IDLE" or state == "DONE" then NewGame() end
        HandleRoll(testPlayer, tonumber(testRoll), DB().minRoll, tonumber(testMax))
        return
    end

    local timeoutPlayer = string.match(message, "^test%s+timeout%s+(%S+)$")
    if timeoutPlayer then
        timeoutTarget = NormalizeName(timeoutPlayer)
        HandleTimeoutExpired()
        return
    end

    Print("Commands:")
    Print("/dr                 - show/hide game UI")
    Print("/dr config          - show/hide config UI")
    Print("/dr new 1000        - start/arm new game")
    Print("/dr roll            - roll expected range")
    Print("/dr invite          - send scoped addon communication join offer")
    Print("/dr join            - request entry from remote host")
    Print("/dr announce        - announce current state")
    Print("/dr report party    - report to auto/say/party/raid/me")
    Print("/dr watch nearby    - accept rolls from visible/party/raid/nearby")
    Print("/dr scope party     - set addon invite scope: target/party/raid")
    Print("/dr timeout 10      - set roll timeout seconds; 0/off disables")
    Print("/dr countdown on    - enable/disable DBM-style countdown popup")
    Print("/dr countdown reset - reset countdown popup position")
    Print("/dr bet 10g 5s 0c   - set bet per player")
    Print("/dr mode reverse    - mode: reverse/classic/elimination/free")
    Print("/dr betmode pot     - bet mode: pot/winner/loser")
    Print("/dr minimap on      - show/hide minimap button")
    Print("/dr versions        - check addon versions in group")
    Print("/dr settlement      - show paid/unpaid settlement panel")
    Print("/dr restore         - restore previous saved session")
    Print("/dr audit           - show last audit entries")
    Print("/dr add/remove/out/next/correct - admin recovery commands")
    Print("/dr test players 4  - dry-run helper commands")
    Print("/dr comm on         - enable/disable addon communication")
    Print("/dr requirejoin on  - host approval popup for addon join requests")
    Print("/dr reset           - reset session")
    Print("/dr lock            - toggle participant lock")
end

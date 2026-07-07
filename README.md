# DeathRollMate 1.6.0

DeathRollMate is a compact Death Roll helper addon for World of Warcraft WotLK 3.3.5a.

## Core rules

- The host starts a game with `/dr new 1000` or the **New Game** button.
- The host is automatically a participant.
- The first valid roll uses the configured starting range, for example `/roll 1-1000`.
- Every accepted roll becomes the next maximum.
- A valid manual `/roll` still auto-joins the roller if auto-join is enabled and participants are not locked.
- Players with the addon can receive target / party / raid addon-comm invites.
- Players without the addon can still join by manually rolling the correct range.

## New in 1.6.0

- Host-authoritative roll synchronization.
- Explicit rejected-roll reasons.
- Game mode presets:
  - Reverse: minimum roll wins.
  - Classic: minimum roll loses.
  - Elimination: timeout / minimum roll loss style.
  - Free: relaxed mode without timeout.
- Bet settlement modes:
  - Pot.
  - Winner takes.
  - Loser pays.
- Settlement panel with paid / unpaid tracking.
- Addon version check.
- Audit log.
- Session restore / discard.
- DBM-style countdown sounds.
- Minimap button.
- Admin recovery commands.
- Dry-run test commands.

## Main commands

```text
/dr                  show/hide game UI
/dr config           show/hide config UI
/dr new 1000         start a new game
/dr roll             roll the expected range
/dr invite           send addon invite using target/party/raid scope
/dr join             accept/request join after addon invite
/dr announce         announce current state
/dr reset            reset session
```

## Configuration commands

```text
/dr mode reverse         reverse/classic/elimination/free
/dr betmode pot         pot/winner/loser
/dr bet 10g 5s 0c       set bet per player
/dr timeout 10          set roll timeout
/dr countdown on        enable countdown popup
/dr countdown reset     reset countdown popup position
/dr report party        auto/say/party/raid/me
/dr watch visible       visible/party/raid/nearby
/dr scope party         target/party/raid invite scope
/dr comm on             enable addon communication
/dr requirejoin on      require host approval popup for addon Join button
/dr lock                toggle participant lock
```

## Diagnostics and recovery

```text
/dr versions            ask group for DeathRollMate versions
/dr settlement          show settlement panel
/dr audit               print last audit entries
/dr restore             restore previous saved session
/dr discard             discard saved session
```

## Admin commands

```text
/dr add PlayerName      add participant manually
/dr remove PlayerName   remove participant manually
/dr out PlayerName      mark participant eliminated
/dr next PlayerName     set expected next roller
/dr correct 437         correct current maximum
```

## Dry-run helpers

```text
/dr test players 4
/dr test roll PlayerA 437 1000
/dr test timeout PlayerB
```

## WotLK limitations

- `/roll` results arrive as `CHAT_MSG_SYSTEM`, not as SAY/PARTY/RAID chat events.
- Addon communication supports PARTY, RAID and WHISPER, but there is no real `/say` addon broadcast.
- Nearby/range checks are only reliable for known unit tokens such as party, raid, target or mouseover.
- The addon does not trade gold automatically; settlement is displayed and tracked manually.

# Front end ↔ Lean contract

**Status: implemented** for the laws the Lean model has (gravity, `maxSpeed`, `maxAcceleration`).
`make serve` runs the Lean server (`ServerMain.lean`, `Paradox/Api.lean`), which answers with the real
`step`. Without it, `web/js/mock-engine.js` answers and the UI says so on screen. The temperature,
bounce and friction laws below are still proposals: the Lean server refuses them until the model has
rules for them.

## What the Lean server adds to this format

- Request fields: `mode` (`"protected"` or `"unprotected"`), `selected` (guarantee ids to protect),
  `randomness` (chance of a random law change per tick, as a fraction string), `eventSeed`, and
  `proof` (the `_proof` of the world being sent, so tracking continues).
- Each frame carries `_proof`: for each guarantee, `{status, since, violatedAt, note}`, where status
  is `proven`, `violated` or `unknown`. `proven` means the state at `since` satisfied it and every
  event since then is covered by its theorem. `violated` means a state computed by `step` breaks it.
  `unknown` means an event outside the theorem's assumptions ran but no state has broken it yet.
- Protected mode rejects an environmental event when a selected guarantee's theorem needs `Allowed`
  and the event fails it, and rejects an edit (`spawnBody`, `removeBody`, `applyImpulse`, `setBody`)
  when the edited world breaks a selected guarantee. Unprotected mode runs both.
- `randomEvents` in the response lists the seeded random events, each `accepted` or not.
- Extra event types: `reverseGravity`, `disableGravity`, `idle`, and
  `setBody` (`id`, optional `position` and `velocity`).
- Each environmental event takes one tick, because Lean's `step` is `tick ∘ applyEvent`.

## Ground rules

- **Lean is the only physics.** The browser never computes a state it shows as real. It only draws
  states that Lean returns, and animates between them.
- **Numbers are exact.** Every number is a string holding a fraction (`"-981/100"`) or a whole
  number (`"20"`). The browser converts to decimals for drawing only.
- **The server keeps no state.** Each request carries the world; each answer carries the next worlds.
- **Rounding is part of the rules.** Friction and cooling multiply by fractions every tick, so exact
  denominators would grow without limit. `step` should round every position, velocity and
  temperature to a multiple of `1/1000` at the end of each tick. The proofs then cover the rounding.

## One endpoint

`POST /api/step`

Request:

```json
{
  "world": { ... },
  "events": [ { "type": "setLaw", "law": "freezingPoint", "value": "-20" } ],
  "ticks": 30
}
```

`events` are applied, in order, before the first tick. Then the world advances `ticks` times.

Response:

```json
{
  "frames": [ { ... world after tick 1 ... }, { ... after tick 2 ... } ],
  "rejected": [
    { "index": 0, "event": { ... }, "reason": "The freezing point must be below the boiling point.",
      "protects": "phase-matches-temperature" }
  ],
  "guarantees": [ ... see below ... ],
  "engine": "lean"
}
```

A rejected event changes nothing; the others still apply. `index` is the event's position in the
request's `events` list. Events may carry extra fields (the UI adds `name` to `spawnBody`); ignore them. `engine` is `"lean"` or `"mock"`.

`GET /api/world?seed=492018` returns a starting world: `{ "world": { ... } }`.

## The world

```json
{
  "tick": 0,
  "bounds": { "min": ["-10", "0", "-10"], "max": ["10", "15", "10"] },
  "laws": {
    "gravity": ["0", "-981/100", "0"],
    "maxSpeed": "30",
    "maxAcceleration": "40",
    "timeStep": "1/60",
    "restitution": "7/10",
    "drag": "1/200",
    "freezingPoint": "0",
    "boilingPoint": "100",
    "ambientTemperature": "20",
    "heatTransfer": "1/100"
  },
  "bodies": [
    { "id": 0, "material": "water", "phase": "solid",
      "position": ["0", "8", "0"], "velocity": ["0", "0", "0"],
      "mass": "1", "temperature": "-10" }
  ]
}
```

`material` is `"water"` (changes phase) or `"rubber"` (never changes phase; `phase` is always
`"solid"`). `phase` is `"solid"`, `"liquid"` or `"gas"`.

## Events

| `type` | Fields | Allowed when |
|---|---|---|
| `idle` | | always |
| `setGravity` | `value: [x, y, z]` | always (acceleration is capped) |
| `setLaw` | `law`, `value` | see the law table |
| `spawnBody` | `body` (as in the world, without `id`; Lean picks the id) | inside the box, mass > 0, temperature ≥ absolute zero, each speed component ≤ `maxSpeed` |
| `removeBody` | `id` | a body with that id exists |
| `applyImpulse` | `id`, `value: [x, y, z]` | a body with that id exists (the result is capped at `maxSpeed`) |

## Laws

The first four exist in Lean today. The rest are new.

| Law | UI name | Meaning | Allowed values |
|---|---|---|---|
| `gravity` | Gravity, Wind | acceleration on every body | any (capped by `maxAcceleration`) |
| `maxSpeed` | Speed of light | no velocity component may exceed it | > 0 |
| `maxAcceleration` | Max force | cap on each acceleration component | ≥ 0 |
| `timeStep` | Time speed | seconds per tick | > 0 |
| `restitution` | Bounciness | at a wall, the velocity on that axis flips and is multiplied by this. Liquids use 0. | 0 to 1 |
| `drag` | Air friction | each tick, velocity is multiplied by `1 - drag` | 0 to 1 |
| `freezingPoint` | Freezing point | water below it is solid | above absolute zero, below `boilingPoint` |
| `boilingPoint` | Boiling point | water at or above it is gas | above `freezingPoint` |
| `ambientTemperature` | Room temperature | what bodies warm or cool toward | ≥ absolute zero |
| `heatTransfer` | Heat transfer | each tick, `T += heatTransfer × (ambient − T)` | 0 to 1 |

Absolute zero is `-273`, fixed.

How phase changes motion:

- **Solid:** normal gravity; bounces with `restitution`.
- **Liquid:** normal gravity; does not bounce (restitution 0).
- **Gas:** rises: its acceleration is gravity × `-1/2`.

## Guarantees

The server lists what holds for the current rules. The UI shows exactly this; it never decides a
status itself.

```json
{ "id": "speed-limit", "text": "Nothing moves faster than the speed of light.",
  "status": "proved", "theorem": "boundedVelocity_preservesAll",
  "assumes": "Every event was allowed." }
```

`status` is one of:

- `proved`: proved in Lean for every sequence of allowed events.
- `conditional`: proved, but only under an assumption that the current rules may not meet; `assumes`
  says which.
- `counterexample`: a concrete run breaks it (experimental mode only).
- `unproved`: planned or not yet proved. Never shown as true.

Guarantees the front end expects. The first three exist today; the rest come with the new laws.

| `id` | Text | Lean theorem |
|---|---|---|
| `in-the-box` | Every body stays inside the box. | `boundedPosition_preservesAll` (exists) |
| `speed-limit` | Nothing moves faster than the speed of light. | `boundedVelocity_preservesAll` (exists) |
| `positive-mass` | Every body keeps a positive mass. | `positiveMass_preservesAll` (exists) |
| `phase-matches-temperature` | Ice is never above the freezing point, and steam is never below the boiling point. | new |
| `above-absolute-zero` | Nothing gets colder than absolute zero. | new |
| `no-overshoot` | Cooling never carries a body past room temperature. | new |
| `bounce-no-speedup` | Hitting a wall never makes a body faster. | new |

## Proposed split

- **Lean (teammate):** the new laws and their `Allowed` rules, rounding, the new theorems, and an
  HTTP server for `/api/step` and `/api/world`.
- **Front end (Chirag):** everything in `web/`, built against `mock-engine.js` until the server is up.

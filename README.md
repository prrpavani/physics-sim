# PARADOX

**Build a universe. Change its laws. Prove it makes sense.**

PARADOX lets people invent their own laws of physics, however strange: gravity that pushes, objects
that get heavier as they speed up, space that loops, portals that multiply speed, collisions that
create new objects. Lean 4 then answers a surprisingly deep question: which claims about that
universe are actually justified?

It does not enforce real physics. A strange law is fine, as long as it is well defined and its
claims hold. When a claim fails, you get a concrete run to watch, checked against the formal model.

Everything on screen comes from the Lean model: the browser only draws the exact states it returns,
and blends between them for smooth motion.

## Run it

Requires [elan](https://github.com/leanprover/elan). The first install downloads about 7 GB of
Mathlib cache.

    make install   # fetch Mathlib, build everything, check every proof and test
    make run       # start the app, then open http://127.0.0.1:8787

Click **Guided demo** for the story. `make demo` runs the same story against the API in a terminal.

## What you can change

| Law | Options |
|---|---|
| Force between objects | **Any formula you write**, from mass, charge, distance and speed |
| Newton's third law | Reaction factor: 1 is normal, 0 means nothing pulls back |
| Gravity and fields | Any direction or strength; regional fields that add together |
| Other forces | Drag (including negative), central force, magnetic field and charge |
| Collisions | Pass through, bounce, swap velocity, swap mass, merge, or create a new object |
| Space | Solid walls or looping space; three ways of measuring distance |
| Time | Time step, time reversal, regions where time runs at a different rate |
| Mass | Growth or decay per step; rules that set mass from a formula |
| Portals | Any entrance and exit; reverse, rotate or multiply velocity |
| Rules | Conditions and actions: create, destroy, teleport, scale, and more, in sequence |

Twenty presets are included. See [docs/API.md](docs/API.md).

## The three questions

| Layer | Question | Example of a failure |
|---|---|---|
| Rule consistency | Can the constraints all be true of a universe with an object? | "Stationary" and "moves at 5" |
| Transition consistency | Do the rules say what happens next? | A portal with no destination |
| Evolution consistency | Do guarantees survive as the universe changes? | A ×100 rule breaks a speed limit |

Each result is one of five statuses, each with a precise meaning: `proven`, `counterexample`,
`unknown`, `underspecified`, `inconsistent`. Failing to prove something gives `unknown`. It never
counts as false.

## What is proved

All of these are machine-checked. [Challenge.lean](Paradox/Comparator/Challenge.lean) lists the main
statements with no proofs in the way.

| Theorem | What it says |
|---|---|
| `run_inv` | A guarantee survives any finite list of permitted events. |
| `protectedRun_safe` | In protected mode, **no** list of events can break a guarantee. |
| `next_inv` | A guarantee holds whatever order the rules run in. |
| `random_chaos_safe` | Every seeded random experiment keeps every guarantee, for every seed. |
| `generateWorld_guaranteed` | The universe from any seed starts with every guarantee true. |
| `Rule.keeps_sound` | If the rule checker clears a rule, the rule keeps the guarantee. |
| `pairForces_conserve_momentum` | With Newton's third law on, **every force law anyone can invent** keeps momentum. |
| `interaction_conserves_momentum` | Forces and bounce or merge collisions never change total momentum. |
| `idleRun_energy_le` | With no forces, energy can only stay level or fall, even with walls and portals. |
| `bouncePair_energy_elastic` | A bounce at restitution 1 keeps energy exactly. |
| `idleRun_conserves_mass` | Total mass stays the same as time passes, under the stated laws. |
| `verifyProperty_proven` | A `proven` verdict from the API is correct. |
| `checkTrace_sound` | A checked counterexample really happens and really breaks the claim. |
| `proven_excludes_counterexample` | A proof and a counterexample with permitted events cannot both exist. |
| `checkConstraints_satisfiable`, `checkConstraints_contradiction` | Layer A's answers are correct. |
| `orderStatus_conflict`, `LawExpr.divisionsSafe_sound` | Layer B's answers are correct. |
| `moveBody_free`, `moveAxis_bounce_high`, `moveAxis_bounce_low` | With nothing in the way, motion is exact. At a wall, it is exactly a bounce. |
| `wall_never_speeds_up` | A wall can slow a body or turn it around, but never speed it up. |
| `safeChaos_safe` | Safe chaos keeps every guarantee, at any rate and for any seed. |
| `Domains.meadow_run` | The same engine works for a universe that is not physics. |

The guarantees are: positive mass, every object fully inside the world, every velocity component
within the limit, a safe environment, and unique ids.

## Assumptions

A theorem only says what it says. These matter most:

- **`run_inv` needs a good start.** The guarantee holds at the start, the environment is safe, every
  rule has passed the rule checker, and every event is permitted.
- **A permitted event** has meaningful limits: a positive speed limit and time step, restitution from 0
  to 1, a positive mass rate, portals that cannot add speed. New objects must be valid. New rules must
  pass the checker. **Any force formula is permitted.**
- **Momentum theorems cover forces between bodies only.** Walls and gravity do change momentum. The
  audit reports this as a counterexample for a full step.
- **Energy can only fall when there are no forces.** With gravity on, it can rise.

## What the proofs do not say

- **Position and velocity limits partly hold by construction.** Each step ends by limiting them, so
  these theorems show the limits always work, not that free motion stays bounded. `moveBody_free`
  shows the limits leave motion alone unless they must act.
- **Enforced constraints are enforcement.** `enforcedRun_holds` is true because the universe refuses
  changes that would break a constraint, even if that freezes it. It says nothing about the laws.
- **This is not realistic physics, and nothing here is a claim about the real world.** Motion is in
  discrete steps. A cube collides as if it were a sphere. Square roots in formulas are approximate, to
  within 1/1024, and exact in the model as defined. Numbers are rounded to a grid, which is part of the
  model.
- **A `proven` result covers its stated scope only.** Unpermitted events can break any guarantee, and
  `find-counterexample` will show how.
- **`unknown` says nothing.** The rule checker and search are incomplete by design.
- **The frontend is not verified.** Its floating-point drawing and its blending between frames are not
  covered. Proofs cover the exact rational states it receives.

## What is trusted

- The Lean 4 kernel and compiler, and Mathlib v4.35.0.
- The axioms `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, no new axiom and no
  `native_decide`, and `Paradox/Verification/Audit.lean` fails the build if that changes.
- **The JSON and HTTP layer in `Paradox/Api/`, and the UI in `apps/frontend/`.** The API layer is tested,
  including exact round trips, but not proved. A bug in either could misreport a correct result.
- The definitions each theorem depends on. `Audit.lean` pins the list. There are about 110 for
  `guaranteed_run`, because that theorem is about the whole universe. To review it, start with
  `Paradox/Physics/Kinematics.lean` and `Paradox/Rules/Events.lean`.

## How the proofs are checked

These all run in `make install`. A failure stops the build:

- Main theorems are applied to concrete inputs with every hypothesis proved, so none is vacuous.
- Each guarantee is proved false on a bad world.
- `#guard` tests pin exact results for motion, bounces, wrapping, portals, time scaling, collisions and
  the checkers, including a tampered counterexample being refused.
- Axioms and trusted definitions are pinned for each main theorem.

`make comparator` runs `lake check` and `lake comparator` in a Linux container, since both need Linux.
Both pass. `.github/workflows/lean.yml` runs the same script on each push.

## Layout

    Paradox/Engine/         the generic rule engine
    Paradox/Core/           vectors, bodies, worlds, the force formula language
    Paradox/Physics/        one tick of the simulation
    Paradox/Rules/          rules, events, the rule checker, randomness
    Paradox/Invariants/     the guarantees
    Paradox/Consistency/    layers A and B
    Paradox/Verification/   layer C, protected mode, conservation, tests
    Paradox/Domains/        a second domain on the same engine
    Paradox/Comparator/     the main statements, for independent checking
    Paradox/Api/            JSON, routes, the server
    apps/frontend/          the UI source: React, TypeScript, React Three Fiber
    web/                    the built UI, served by the Lean server
    shared/                 TypeScript types, JSON schema, fixtures
    docs/                   API.md and ARCHITECTURE.md

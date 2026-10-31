# PARADOX

PARADOX is a 3D physics sandbox where you invent a universe, change its laws while it runs, and use
[Lean 4](https://lean-lang.org) to prove what stays true no matter what changes.

**Current state:** the Lean formal model and its proofs (Milestone 1). There is no 3D frontend, JSON
interface, rule editor or counterexample search yet.

## Run it

    make install   # fetch the Mathlib cache, build the project, check every proof
    make run       # run the formal model on a demo world and print exact states

Requires [elan](https://github.com/leanprover/elan). Lean and Mathlib versions are pinned in
`lean-toolchain` and `lake-manifest.json`.

## The model

A world is a list of bodies, a box, and a set of laws. All numbers are exact rationals (`ℚ`).
Time moves in discrete steps. One step applies an environmental event, then advances every body:

    step(world, event) = tick(applyEvent(world, event))

    a  = clampAbs(gravity, maxAcceleration)      each component limited to ±maxAcceleration
    v' = clampAbs(v + dt * a, maxSpeed)          each component limited to ±maxSpeed
    p' = clampPoint(bounds, p + dt * v')         moved to the nearest point in the box

Events are a closed list: `idle`, `changeGravity`, `reverseGravity`, `disableGravity`,
`changeMaxSpeed`, `changeMaxAcceleration`. An event is **allowed** unless it sets a speed limit that
is not positive or an acceleration limit that is negative.

The compiled `paradox` program calls the same `step` function that the theorems are about, so the
proofs are about the running code, not about a separate copy of it.

## What is proved

| Property | Meaning | Holds for | Needs before the step |
|---|---|---|---|
| `PositiveMass` | every body has mass > 0 | every event | the property itself |
| `BoundedPosition` | every body is inside the box | every event | the property itself |
| `BoundedVelocity` | every velocity component is within ±maxSpeed | allowed events | the property itself |
| `SafeEnvironment` | box is non-empty, maxSpeed > 0, maxAcceleration ≥ 0, dt > 0 | allowed events | the property itself |

The main results are in [Preservation.lean](Paradox/Verification/Preservation.lean):

- `guaranteed_preservesAll`: one allowed event keeps all four properties true.
- `guaranteed_run`: any finite sequence of allowed events keeps all four properties true.
- `run_preserves`: the same induction for any property preserved by each allowed event.
- `Preserves.comp`: two transitions that each keep a property true still do when run in sequence.
- `negative_maxSpeed_violates_boundedVelocity`: if a world has a body, setting a negative speed
  limit breaks `BoundedVelocity`. This shows that the velocity theorem cannot cover all events.

## What the proofs do not say

- **Position and velocity bounds hold by construction.** `tick` clamps both, so the theorems show
  the clamps work under every allowed event. They do not show that free motion stays bounded.
- **This is not realistic physics.** A body that reaches a wall is held there: it does not bounce,
  and its velocity is not changed by the wall. Bodies pass through each other. Gravity is uniform.
  Spheres and cubes have no size in the model; each body is a single point.
- **Speed is limited per component.** The length of a velocity vector can reach √3 × maxSpeed.
- **Nothing here is a claim about real-world physics.** The theorems are about this model only.
- **The rendered view will be approximate.** When the frontend exists, floating-point numbers will
  be used for drawing only. Proofs cover the exact rational states.

## How we check the proofs mean something

[Examples.lean](Paradox/Verification/Examples.lean) and
[Audit.lean](Paradox/Verification/Audit.lean) are part of the build, so a failure stops it:

- The main theorems are applied to a concrete world and event list with every hypothesis proved.
- Each invariant is proved false on a bad world.
- `#guard` tests pin exact results of `step`, including motion, gravity reversal and wall contact.
- Each main theorem's axioms are pinned, so `sorry` or a new axiom fails the build.
- The definitions each main statement depends on are pinned, so changing that list fails the build.

## What is trusted

- The Lean 4 kernel and compiler, and Mathlib v4.35.0.
- The axioms `propext`, `Classical.choice` and `Quot.sound`. No `native_decide` is used.
- The definitions a theorem's statement depends on, listed in `Audit.lean`. Read these to know what
  a theorem says. Start with `Paradox/Physics/Kinematics.lean` and `Paradox/Rules/Events.lean`.

**Comparator has not been run.** `lake check` and `lake comparator` sandbox the project and work on
Linux only, and this work was done on macOS.

## Layout

    Paradox/Core/          vectors, bodies, boundaries, worlds
    Paradox/Physics/       tick
    Paradox/Rules/         events, step, run, Allowed
    Paradox/Invariants/    the four properties
    Paradox/Verification/  theorems, examples, audit
    Main.lean              demo executable

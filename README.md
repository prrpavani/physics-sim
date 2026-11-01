# PARADOX

**Change the laws of a universe. See what Lean can prove.**

Move a few sliders: gravity, the pull between objects, Newton's third law, bounciness, a speed
multiplier. Four promises about the universe flip as you do. Each one is either proved by Lean, broken by
a run you can replay, or honestly left unproven. You can read the real Lean proof for each one on screen.

## Run it

Requires [elan](https://github.com/leanprover/elan). The first install downloads about 7 GB of Mathlib
cache.

    make install
    make run

Then open http://127.0.0.1:8787.

## What to try

| Try | What you see |
|---|---|
| Multiply velocity by 100 | With **Keep it consistent** on, Lean's lock turns the limiter on, and the speed limit stays proved. Turn it off and the limit breaks. Replay the run. |
| Turn on the limiter too | The same ×100 law becomes provably safe. |
| Bounciness above 1 | Walls add speed, so the speed limit breaks. Lean shows a test universe where it happens. |
| Bounciness 2 and multiplier 0.1 | Neither is safe alone, but together they cancel. The answer is **Unproven**, because Lean has no proof and the search found no failure. |
| Pull on, third law off | Momentum breaks. Turn the third law back on, and it is proved for any pull strength. |
| Gravity on | Energy can rise. You cannot have this promise and gravity together. |

## The four promises

| Promise | Proved when |
|---|---|
| Objects stay inside the world | Always |
| Speed limit | The limiter is on, or bounciness ≤ 1 and the multiplier's size ≤ 1 |
| Momentum between objects | Newton's third law is on, or there is no pull |
| Energy never rises | No gravity, no pull, bounciness ≤ 1, and the multiplier's size ≤ 1 |

The conditions and promises are in [Spec.lean](Paradox/Spec.lean), and the proofs are in
[Proofs.lean](Paradox/Proofs.lean). The app reads the proof text from those files, so what you see on
screen is what compiled.

## How the answers are justified

- **Proven:** `verdict_proven_sound` shows the promise holds at every future step.
- **Counterexample:** `checkTrace_sound` shows the run starts from a valid universe, really happens under
  the real step function, and really breaks the promise.
- **Unproven:** neither was established. It never means false.
- **Keep it consistent:** `locked_run_safe` shows no list of law changes can break the speed limit while
  it is on.

The server runs the same `tick` function the theorems are about, compiled from the same source. The
browser only draws what it returns, using floating point for drawing alone.

## What the proofs do not say

- **Staying inside and the limiter hold partly by construction.** Each step ends by keeping objects
  inside, so that theorem shows the limit always works. `free_motion` and `wall_bounce` show the limits
  leave motion alone unless they must act.
- **Momentum covers objects acting on each other.** Gravity and walls do change total momentum.
- **Energy means kinetic energy,** and "never rises" is not conservation. Walls and rounding can remove it.
- **This is a small discrete model, not realistic physics.** Objects are spheres that pass through each
  other. Motion is in steps. Numbers are rounded to a grid, which is part of the model. Nothing here is a
  claim about the real world.

## What is trusted

- The Lean 4 kernel and compiler, and Mathlib v4.35.0.
- The axioms `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry` or `native_decide`.
  [Audit.lean](Paradox/Verification/Audit.lean) fails the build if that changes.
- The JSON and HTTP layer in `Paradox/Api/`, and the UI in `apps/frontend/`. They are tested, not proved. A
  bug in either could misreport a correct result.

`make install` also runs the tests: each theorem applied to a real universe, each promise rejecting a bad
one, exact step results, and a tampered counterexample being refused. `make comparator` runs `lake check`
and `lake comparator` in a Linux container, since both need Linux. CI runs the same script on each push.

## Layout

    Paradox/Spec.lean           the promises and their conditions: start here
    Paradox/Proofs.lean         the main theorems
    Paradox/Verdict.lean        the answers on each card, and the lock
    Paradox/Physics/            one step of a universe
    Paradox/Core/               vectors, objects, worlds
    Paradox/Verification/       supporting lemmas, tests and the audit
    Paradox/Comparator/         the main statements, for independent checking
    Paradox/Api/                JSON, routes and the server
    apps/frontend/              the UI source: React, TypeScript, React Three Fiber
    web/                        the built UI, served by the Lean server. Rebuild with `make frontend`

An earlier, much larger version, with a rule language, custom force formulas, portals and chaos, is kept
at the git tag `full-engine`.

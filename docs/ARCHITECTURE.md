# PARADOX architecture

For anyone working on the code or reviewing the proofs.

## The main idea

The whole backend is one Lean program. The function the theorems are about, `step`, is the same
function that answers API requests, compiled from the same source. There is no separate model and
no second implementation for a proof to drift away from.

```
Browser (React, Three.js)
   │  JSON over HTTP, rationals as strings
   ▼
Paradox/Api      HTTP server, router, JSON            tested, not proved
   │
   ▼
Paradox/Verification, Paradox/Consistency             verdicts, each with a soundness theorem
   │
   ▼
Paradox/Rules, Paradox/Physics, Paradox/Core          the universe: `step`, `Allowed`, `Rule.eval`
   │
   ▼
Paradox/Engine   generic: knows nothing about physics
```

## The modules

| Folder | Holds |
|---|---|
| `Engine/System.lean` | Generic results for any universe: satisfiability, preservation, composition, induction over events, nondeterministic moves, guards, trace checking. |
| `Core/` | Vectors, bodies, boxes, laws, worlds, and `LawExpr`, the language for force formulas. |
| `Physics/` | `tick`: forces, collisions, motion, boundaries, portals, rounding. |
| `Rules/Syntax`, `Semantics` | The rule language and what each rule does. |
| `Rules/Analysis` | The rule checker: reads a rule and answers "safe" or "cannot tell". |
| `Rules/Events` | Every environmental event, `step`, `run` and `Allowed`. |
| `Rules/Random` | Seeded generators of events and worlds. |
| `Invariants/` | The guarantees. |
| `Consistency/` | Layer A (`Constraints`) and Layer B (`Transitions`). |
| `Verification/` | Layer C: preservation, rule checker soundness, conservation, verdicts, protected mode, and tests. |
| `Domains/Ecosystem` | A second, non-physics universe on the same engine. |
| `Comparator/` | The main statements alone, and their proofs, for `lake comparator`. |
| `Api/` | JSON, the router, the theorem catalog, presets, fixtures and the HTTP server. |

## One step

```
step w e = evalRules w rules (tick (applyEvent w e))
```

`tick` does the following to each body, in order:

1. Add external acceleration: gravity, fields, central force, drag and magnetism.
2. Apply the invented force between each pair of bodies.
3. Apply the collision mode to touching bodies.
4. Limit each velocity component to the speed limit.
5. Move. At a boundary, bounce or wrap around.
6. Go through a portal, if the body landed in one.
7. Round position and velocity toward zero, to the grid.
8. Bring the position fully inside the world.
9. Multiply mass by the mass rate.

Rules run after the bodies move, so a rule that breaks a limit leaves the world visibly broken. That
is what makes its counterexample real. Rules live in the world, and adding one is an event, so
protected mode checks new rules the same way it checks everything else.

## Three layers, kept separate

| Layer | Question | Function | Key theorems |
|---|---|---|---|
| A: rules | Can the constraints hold in a universe with an object? | `checkConstraints` | `checkConstraints_satisfiable`, `checkConstraints_contradiction` |
| B: transitions | Do the rules say what happens, without a default? | `checkTransitions` | `divisionsSafe_sound`, `orderStatus_conflict`, `orderStatus_independent` |
| C: evolution | Do guarantees survive change? | `verifyClaim` | `run_inv`, `next_inv`, `verifyProperty_proven`, `checkTrace_sound` |

An empty universe trivially meets every "every object must..." constraint. So Layer A asks for at
least one object.

## How an answer stays honest

A check is not sound because it is careful. It is sound because a theorem says so:

- A `proven` verdict: `verifyProperty_proven` says the guarantee holds after every permitted event
  list.
- A `counterexample`: search only proposes traces. `checkTrace` replays each through `step`, and
  `checkTrace_sound` says what passes really happens and really breaks the claim.
- A cleared rule: `Rule.keeps_sound` covers every rule anyone can write.
- `unknown`: the only result with no theorem. It claims nothing.

Theorem ids in responses are compile-checked names, so a renamed or deleted theorem fails the build.

## Why one theorem covers every force law

`forcePair` works out the force value once per pair, then applies it to one body, and the opposite
way, times `reaction`, to the other. Momentum between the two cancels by algebra alone, whatever the
value is. So `pairForces_conserve_momentum` holds for every `LawExpr`, including ones nobody has
invented yet.

The bounds work the same way. Every step ends by limiting velocity and position, so they hold for
any force formula. `Reference.lean` shows these limits are not hiding the physics: with nothing in
the way, a move is exactly textbook motion, and a wall hit is exactly a bounce.

## Decisions

- **The server is in Lean, not Node.** `Std.Http` ships with Lean 4.35. This leaves no second language
  in the backend and matches the hackathon's preference for code proved in Lean.
- **Exact rationals, with a rounding grid in the model.** Bounces and collisions divide, so exact
  numbers grow without limit. The grid is part of the formal model and rounds toward zero, which never
  increases a magnitude, so speed and energy results still hold.
- **Mathlib stays.** It costs a 7 GB cache, but `field_simp`, `nlinarith` and `linarith` carry the
  conservation proofs.
- **Lean files stay at the repo root**, not in `formal/`. It keeps `lake` and the Makefile simple. The
  frontend belongs in `apps/frontend/`.
- **Division by zero gives zero.** Lean functions must be total. Layer B reports when a universe relies
  on this.
- **Protected-mode constraints work by enforcement.** `enforcedRun_holds` is true for any constraint
  because the universe refuses changes. It says nothing about the laws keeping the constraint alone,
  and the API must say so.

## Adding things

**A new event:** add it to `EnvironmentEvent`, `applyEvent` and `Allowed` if it needs a condition, and
to `encEvent` and `decEvent`. Lean's exhaustive matching points to each proof that must change.

**A new rule action:** add it to the syntax, `apply`, the checker and the JSON. The checker's soundness
proof fails until the new case is covered, so an unsafe rule cannot be cleared by mistake.

**A new domain:** define the state and step, and prove `PreservesAll`. The engine provides the rest.
See `Domains/Ecosystem.lean`.

import Paradox.Verification.Preservation

/-!
# Sanity checks on the theorems

These guard against theorems that are true for uninteresting reasons:

* The main theorems are applied to a concrete world with every hypothesis proved, so their
  hypotheses can be met.
* Each invariant is shown to reject a bad world, so no invariant is trivially true.
* The `#guard`s pin exact transition values, so a `tick` that did nothing would fail the build.
-/

namespace Paradox

/-- A 10 × 10 × 10 box with two moving spheres. -/
def demoWorld : World where
  bodies :=
    [ { position := ⟨0, 5, 0⟩, velocity := ⟨1, 0, 0⟩, mass := 1 },
      { position := ⟨-2, 1, 3⟩, velocity := ⟨0, 2, -1⟩, mass := 3 / 2 } ]
  bounds := { minX := -5, maxX := 5, minY := 0, maxY := 10, minZ := -5, maxZ := 5 }
  laws := { gravity := ⟨0, -10, 0⟩, maxSpeed := 20, maxAcceleration := 30, timeStep := 1 / 10 }

/-! ## The hypotheses can be met -/

theorem demoWorld_guaranteed : Guaranteed demoWorld := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [PositiveMass, demoWorld]
  · norm_num [BoundedPosition, Bounds.Contains, demoWorld]
  · norm_num [BoundedVelocity, Vec3.WithinAbs, demoWorld]
  · norm_num [SafeEnvironment, Bounds.Valid, demoWorld]

/-- An event sequence that strengthens, reverses and removes gravity and lowers the speed limit. -/
def demoEvents : List EnvironmentEvent :=
  [.changeGravity ⟨0, -100, 0⟩, .reverseGravity, .changeMaxSpeed (1 / 2), .disableGravity, .idle]

/-- `guaranteed_run` applied to a concrete world and event sequence. -/
example : Guaranteed (run demoWorld demoEvents) :=
  guaranteed_run demoWorld demoEvents demoWorld_guaranteed (by
    norm_num [demoEvents, AllowedTrace, Allowed])

/-- `negative_maxSpeed_violates_boundedVelocity` applied to a concrete world. -/
example : ¬ BoundedVelocity (step demoWorld (.changeMaxSpeed (-1))) :=
  negative_maxSpeed_violates_boundedVelocity demoWorld (by norm_num) (by simp [demoWorld])

/-! ## The invariants reject bad worlds -/

/-- A body with zero mass is rejected. -/
example : ¬ PositiveMass { demoWorld with
    bodies := [{ position := ⟨0, 5, 0⟩, velocity := Vec3.zero, mass := 0 }] } := by
  norm_num [PositiveMass]

/-- A body just outside the box is rejected. -/
example : ¬ BoundedPosition { demoWorld with
    bodies := [{ position := ⟨6, 5, 0⟩, velocity := Vec3.zero, mass := 1 }] } := by
  norm_num [BoundedPosition, Bounds.Contains, demoWorld]

/-- A body just over the speed limit is rejected. -/
example : ¬ BoundedVelocity { demoWorld with
    bodies := [{ position := ⟨0, 5, 0⟩, velocity := ⟨21, 0, 0⟩, mass := 1 }] } := by
  norm_num [BoundedVelocity, Vec3.WithinAbs, demoWorld]

/-- A zero speed limit is rejected. -/
example : ¬ SafeEnvironment { demoWorld with laws.maxSpeed := 0 } := by
  norm_num [SafeEnvironment]

/-! ## Exact transition values -/

-- The first sphere falls under gravity: v = (1, -1, 0), p = (1/10, 49/10, 0).
#guard (step demoWorld .idle).bodies.head? ==
  some { position := ⟨1 / 10, 49 / 10, 0⟩, velocity := ⟨1, -1, 0⟩, mass := 1 }

-- Reversing gravity changes the direction of the velocity update in the same step.
#guard (step demoWorld .reverseGravity).bodies.head? ==
  some { position := ⟨1 / 10, 51 / 10, 0⟩, velocity := ⟨1, 1, 0⟩, mass := 1 }

-- A body is held at the wall: a large time step makes it overshoot, and the clamp catches it.
#guard (step { demoWorld with laws.timeStep := 10 } .idle).bodies.head? ==
  some { position := ⟨5, 0, 0⟩, velocity := ⟨1, -20, 0⟩, mass := 1 }

-- Lowering the speed limit takes effect immediately.
#guard ((step demoWorld (.changeMaxSpeed (1 / 2))).bodies.head?.map (·.velocity)) ==
  some ⟨1 / 2, -1 / 2, 0⟩

-- The runnable `Allowed` check gives the right answer on both sides of the limit.
#guard decide (Allowed demoWorld (.changeMaxSpeed 1))
#guard !decide (Allowed demoWorld (.changeMaxSpeed 0))
#guard decide (AllowedTrace Allowed demoWorld demoEvents)
#guard !decide (AllowedTrace Allowed demoWorld [.reverseGravity, .changeMaxSpeed (-1)])

end Paradox

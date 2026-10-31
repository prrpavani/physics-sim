import Paradox.Generate

/-!
# Checks on concrete worlds

These show that the hypotheses of the main theorems can be met, that the spec rejects bad
worlds, and that `step` does what its comments say.
-/

namespace Paradox

/-- A small world: 10 × 8 cells, speed limit 2, gravity pulling down, two bodies, one portal. -/
def demoWorld : World where
  width := 10
  height := 8
  maxSpeed := 2
  gravity := ⟨0, 1⟩
  bodies := [⟨0, ⟨1, 1⟩, ⟨1, 0⟩, 2⟩, ⟨1, ⟨2, 1⟩, ⟨-1, 0⟩, 2⟩]
  portals := [⟨⟨9, 7⟩, ⟨0, 0⟩⟩]
  tick := 0

-- The hypothesis `SafeWorld w` can be met.
example : SafeWorld demoWorld := by decide
example : SafeWorld (generateWorld 492018) := by decide

-- The spec rejects bad worlds.
/-- A body off the right edge. -/
example : ¬ SafeWorld { demoWorld with bodies := [⟨0, ⟨10, 1⟩, ⟨0, 0⟩, 1⟩] } := by decide
/-- Two bodies with the same id. -/
example : ¬ SafeWorld { demoWorld with bodies := [⟨0, ⟨1, 1⟩, ⟨0, 0⟩, 1⟩, ⟨0, ⟨2, 2⟩, ⟨0, 0⟩, 1⟩] } := by decide
/-- A body faster than the speed limit. -/
example : ¬ SafeWorld { demoWorld with bodies := [⟨0, ⟨1, 1⟩, ⟨3, 0⟩, 1⟩] } := by decide
/-- A portal that leads off the grid. -/
example : ¬ SafeWorld { demoWorld with portals := [⟨⟨1, 1⟩, ⟨1500, 500⟩⟩] } := by decide
/-- A speed limit as wide as the world: one bounce could land outside. -/
example : ¬ SafeWorld { demoWorld with maxSpeed := 10 } := by decide

-- Bouncing: a body at 9 moving +2 in a 10-wide world hits the wall and lands at 7, moving -2.
#guard bounce 10 9 2 == (7, -2)
#guard bounce 10 1 (-2) == (1, 2)
#guard bounce 10 4 2 == (6, 2)
-- Speeds are capped.
#guard capSpeed 2 5 == 2
#guard capSpeed 2 (-7) == -2

-- The engine rejects rule-breaking events.
#guard (step demoWorld (.spawnBody ⟨5, ⟨20, 1⟩, ⟨0, 0⟩, 1⟩)).isNone   -- off the grid
#guard (step demoWorld (.spawnBody ⟨0, ⟨3, 3⟩, ⟨0, 0⟩, 1⟩)).isNone    -- id 0 is taken
#guard (step demoWorld (.spawnBody ⟨5, ⟨3, 3⟩, ⟨0, 0⟩, 0⟩)).isNone    -- no mass
#guard (step demoWorld (.addPortal ⟨⟨1, 1⟩, ⟨1500, 500⟩⟩)).isNone      -- portal off the grid
#guard (step demoWorld (.collide 0 0)).isNone                           -- a body with itself
#guard (step demoWorld (.removeBody 7)).isNone                          -- no such body
-- ...and accepts lawful ones, including absurd gravity.
#guard (step demoWorld (.collide 0 1)).isSome
#guard (execute demoWorld [.changeGravity ⟨0, -1000⟩, .move, .move, .applyImpulse 0 ⟨99, 99⟩, .move]).isSome

-- The hypothesis of `execute_preserves_safe` can be met: this run is accepted, and ends safe.
example : (execute demoWorld [.changeGravity ⟨0, -1000⟩, .move, .applyImpulse 0 ⟨99, 99⟩, .move]).any
    (fun w => decide (SafeWorld w)) := by decide

end Paradox

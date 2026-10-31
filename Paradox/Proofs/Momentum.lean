import Paradox.Step

/-!
# Momentum

A collision between two equal-mass bodies swaps their velocities, so the total momentum of
the world does not change. This holds only for the `collide` event: gravity, pushes and walls
add or remove momentum, as they would in real physics.
-/

namespace Paradox

/-- Theorem 2: an accepted collision does not change the world's total momentum. -/
theorem collide_preserves_momentum {w w' : World} {a b : Nat}
    (h : SafeWorld w) (hstep : step w (.collide a b) = some w') :
    totalMomentum w'.bodies = totalMomentum w.bodies := by
  sorry

end Paradox

import Paradox.Generate

/-!
# Every generated world is safe
-/

namespace Paradox

/-- Theorem 5: the world built from any seed is safe. -/
theorem generated_world_safe (seed : Nat) : SafeWorld (generateWorld seed) := by
  sorry

end Paradox

import Paradox.Core.World

namespace Paradox

/-- The boundaries and laws satisfy their required preconditions. -/
def SafeEnvironment (w : World) : Prop :=
  w.bounds.Valid ∧
  0 < w.laws.maxSpeed ∧
  0 ≤ w.laws.maxAcceleration ∧
  0 < w.laws.timeStep

end Paradox

import Paradox.Core.World

namespace Paradox

/-- Every body has positive mass. -/
def PositiveMass (w : World) : Prop :=
  ∀ b ∈ w.bodies, 0 < b.mass

instance (w : World) : Decidable (PositiveMass w) := by unfold PositiveMass; infer_instance

end Paradox

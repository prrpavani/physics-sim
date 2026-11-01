import Paradox.Core.World

namespace Paradox

/-- Every body is fully inside the world's boundaries. -/
def BoundedPosition (w : World) : Prop :=
  ∀ b ∈ w.bodies, (w.bounds.inset b.extent).Contains b.position

instance (w : World) : Decidable (BoundedPosition w) := by unfold BoundedPosition; infer_instance

end Paradox

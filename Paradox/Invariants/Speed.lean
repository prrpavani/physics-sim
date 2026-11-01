import Paradox.Core.World

namespace Paradox

instance (a : Vec3) (m : ℚ) : Decidable (a.WithinAbs m) := by unfold Vec3.WithinAbs; infer_instance

/-- Every velocity component of every body is within the world's current speed limit. -/
def BoundedVelocity (w : World) : Prop :=
  ∀ b ∈ w.bodies, b.velocity.WithinAbs w.laws.maxSpeed

instance (w : World) : Decidable (BoundedVelocity w) := by unfold BoundedVelocity; infer_instance

end Paradox

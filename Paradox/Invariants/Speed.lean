import Paradox.Core.World

namespace Paradox

/-- Every velocity component of every body is within the world's current speed limit. -/
def BoundedVelocity (w : World) : Prop :=
  ∀ b ∈ w.bodies, b.velocity.WithinAbs w.laws.maxSpeed

end Paradox

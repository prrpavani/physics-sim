import Paradox.Core.World

namespace Paradox

/-- Every body has positive mass. -/
def PositiveMass (w : World) : Prop :=
  ∀ b ∈ w.bodies, 0 < b.mass

end Paradox

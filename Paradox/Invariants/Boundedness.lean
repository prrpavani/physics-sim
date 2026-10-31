import Paradox.Core.World

namespace Paradox

/-- Every body is inside the world's boundaries. -/
def BoundedPosition (w : World) : Prop :=
  ∀ b ∈ w.bodies, w.bounds.Contains b.position

end Paradox

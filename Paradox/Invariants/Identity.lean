import Paradox.Core.World

namespace Paradox

/-- No two bodies share an id, and every id is below the next id to be given out. -/
def UniqueIds (w : World) : Prop :=
  (w.bodies.map Body.id).Nodup ∧ ∀ b ∈ w.bodies, b.id < w.nextId

instance (w : World) : Decidable (UniqueIds w) := by unfold UniqueIds; infer_instance

end Paradox

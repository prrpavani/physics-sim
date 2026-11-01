import Paradox.Invariants.Mass
import Paradox.Invariants.Boundedness
import Paradox.Invariants.Speed
import Paradox.Invariants.Identity
import Paradox.Invariants.Environment

namespace Paradox

/-- The guarantees a user can ask for. -/
inductive Property where
  | positiveMass
  | boundedPosition
  | boundedVelocity
  | safeEnvironment
  | uniqueIds
  deriving DecidableEq, Repr

/-- What each guarantee says about a world. -/
def Property.holds : Property → World → Prop
  | .positiveMass, w => PositiveMass w
  | .boundedPosition, w => BoundedPosition w
  | .boundedVelocity, w => BoundedVelocity w
  | .safeEnvironment, w => SafeEnvironment w
  | .uniqueIds, w => UniqueIds w

instance (p : Property) (w : World) : Decidable (p.holds w) := by
  cases p <;> unfold Property.holds <;> infer_instance

/-- Every guarantee. -/
def Property.all : List Property :=
  [.positiveMass, .boundedPosition, .boundedVelocity, .safeEnvironment, .uniqueIds]

theorem Property.mem_all (p : Property) : p ∈ Property.all := by
  cases p <;> simp [Property.all]

end Paradox

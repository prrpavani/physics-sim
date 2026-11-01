import Paradox.Physics.Kinematics

namespace Paradox

/-- A wall can slow a body down or turn it around, but never speed it up: after the tick, each
velocity component is no larger in size than it was just before the body reached the wall. -/
def WallNeverSpeedsUp (laws : PhysicsLaws) (bounds : Bounds) (b : Body) : Prop :=
  let before := freeVelocity laws b
  let after := (tickBody laws bounds b).velocity
  |after.x| ≤ |before.x| ∧ |after.y| ≤ |before.y| ∧ |after.z| ≤ |before.z|

end Paradox

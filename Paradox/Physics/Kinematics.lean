import Paradox.Core.World

/-!
# One tick of the simulation

Semi-implicit Euler with component-wise clamping, then a bounce off any wall the body hit:

    a  = clampAbs(gravity, maxAcceleration)
    v  = clampAbs(v + dt * a, maxSpeed)              the velocity just before any wall
    p' = clampPoint(bounds, p + dt * v)              a body that would leave stops at the wall
    v' = v on each axis where the body stayed inside;
         roundTowardZero(-(e * v)) on each axis where it hit a wall,
         where e = clamp(restitution, 0, 1)

Collisions between bodies are not modelled.
-/

namespace Paradox

/-- A body's velocity after gravity acts, before it meets any wall. -/
def freeVelocity (laws : PhysicsLaws) (b : Body) : Vec3 :=
  let acceleration := laws.gravity.clampAbs laws.maxAcceleration
  (b.velocity.add (acceleration.scale laws.timeStep)).clampAbs laws.maxSpeed

/-- Bounces are rounded toward zero to a multiple of `1 / bounceGrid`. -/
def bounceGrid : ℕ := 1000

/-- The velocity along one axis after the walls `lo` and `hi`. If the body's target `p` stayed
between them, `v` is unchanged. Otherwise the body bounced: `v` reverses and is scaled by the
bounciness `e`, rounded toward zero. -/
def wallComponent (e lo hi p v : ℚ) : ℚ :=
  if p < lo ∨ hi < p then roundTowardZero bounceGrid (-(e * v)) else v

/-- Advance one body by one time step. Only its position and velocity change. -/
def tickBody (laws : PhysicsLaws) (bounds : Bounds) (b : Body) : Body :=
  let velocity := freeVelocity laws b
  let target := b.position.add (velocity.scale laws.timeStep)
  let e := clamp laws.restitution 0 1
  { b with
    position := bounds.clampPoint target
    velocity :=
      ⟨wallComponent e bounds.minX bounds.maxX target.x velocity.x,
       wallComponent e bounds.minY bounds.maxY target.y velocity.y,
       wallComponent e bounds.minZ bounds.maxZ target.z velocity.z⟩ }

/-- Advance every body by one time step. Bounds and laws do not change. -/
def tick (w : World) : World :=
  { w with bodies := w.bodies.map (tickBody w.laws w.bounds) }

end Paradox

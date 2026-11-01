import Paradox.Physics.Forces
import Paradox.Physics.Snap

/-!
# One step of a universe

Each step does the following, in this order:

1. Gravity and the pull between objects change velocities.
2. Each velocity component is limited to the speed limit.
3. Objects move. An object that would pass through a wall stops there and bounces.
4. Positions and velocities are rounded to the grid, and each position is kept inside the world.
5. Every velocity is multiplied by the multiplier.
6. If the limiter is on, the speed limit is enforced again.

Objects pass through each other.
-/

namespace Paradox

/-- Limit a body's velocity to the speed limit. -/
def limitSpeed (l : Laws) (b : Body) : Body :=
  { b with velocity := b.velocity.clampAbs l.maxSpeed }

/-- Move along one axis, with walls at `lo` and `hi`. Returns the new position and velocity. An object
that would pass through a wall stops at the wall, and its velocity reverses and scales by `e`. -/
def moveAxis (e dt lo hi p v : ℚ) : ℚ × ℚ :=
  let target := p + dt * v
  if target < lo then (lo, -(e * v))
  else if hi < target then (hi, -(e * v))
  else (target, v)

/-- Move one body and keep it inside the world. -/
def moveBody (w : World) (b : Body) : Body :=
  let l := w.laws
  let room := w.bounds.inset b.radius
  let x := moveAxis l.restitution l.timeStep room.minX room.maxX b.position.x b.velocity.x
  let y := moveAxis l.restitution l.timeStep room.minY room.maxY b.position.y b.velocity.y
  let z := moveAxis l.restitution l.timeStep room.minZ room.maxZ b.position.z b.velocity.z
  { b with
    position := room.clampPoint ((Vec3.mk x.1 y.1 z.1).snap l.grid)
    velocity := (Vec3.mk x.2 y.2 z.2).snap l.grid }

/-- Apply the multiplier, then the limiter if it is on. -/
def finishBody (l : Laws) (b : Body) : Body :=
  let v := b.velocity.scale l.multiplier
  { b with velocity := if l.limiter then v.clampAbs l.maxSpeed else v }

/-- Gravity and pull for all bodies. -/
def forcesStage (l : Laws) (bs : List Body) : List Body :=
  pullStage l (bs.map (applyGravity l))

/-- One step of the universe. The laws and the box do not change. -/
def tick (w : World) : World :=
  { w with
    bodies := (((forcesStage w.laws w.bodies).map (limitSpeed w.laws)).map (moveBody w)).map
      (finishBody w.laws)
    tick := w.tick + 1 }

/-- `n` steps of the universe. -/
def run : Nat → World → World
  | 0, w => w
  | n + 1, w => run n (tick w)

end Paradox

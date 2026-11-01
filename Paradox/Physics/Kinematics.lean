import Paradox.Physics.Collision
import Paradox.Physics.Forces
import Paradox.Physics.Snap

/-!
# One tick of the simulation

A tick does the following to every body, in this order:

1. Add external acceleration to its velocity: gravity, fields, central force, drag, magnetism.
2. Apply the invented force between each pair of bodies.
3. Apply the collision mode to bodies that are touching.
4. Limit each velocity component to the speed limit.
5. Move the body. At a boundary, it bounces or wraps around, depending on the topology.
6. Send it through a portal if it landed in one.
7. Round position and velocity to the grid.
8. Bring its position fully inside the world.
9. Multiply its mass by the mass rate.
-/

namespace Paradox

/-- Limit a body's velocity to the speed limit. -/
def limitSpeed (laws : PhysicsLaws) (b : Body) : Body :=
  { b with velocity := b.velocity.clampAbs laws.maxSpeed }

/-- Move `x` toward the interval from `lo` to `hi` by adding or subtracting its width. -/
def wrap (lo hi x : ℚ) : ℚ :=
  if lo < hi then
    x - (hi - lo) * (⌊(x - lo) / (hi - lo)⌋ : ℚ)
  else lo

/-- Step 5 on one axis, for boundaries at `lo` and `hi`. Returns the new position and velocity.
In a box, a body that would pass through a wall stops at the wall, and its velocity reverses and
shrinks by `e`. In a torus, it comes back on the other side at the same velocity. -/
def moveAxis (topology : Topology) (e dt lo hi p v : ℚ) : ℚ × ℚ :=
  let target := p + dt * v
  match topology with
  | .box =>
    if target < lo then (lo, -(e * v))
    else if hi < target then (hi, -(e * v))
    else (target, v)
  | .torus =>
    if target < lo ∨ hi < target then (wrap lo hi target, v) else (target, v)

/-- The velocity after passing through a portal with this effect. -/
def PortalEffect.apply : PortalEffect → Vec3 → Vec3
  | .none, v => v
  | .reverse, v => v.neg
  | .rotate, v => ⟨v.z, v.y, -v.x⟩
  | .scale k, v => v.scale k

/-- The first portal whose entrance contains `p`, if there is one. -/
def portalAt (portals : List Portal) (p : Vec3) : Option Portal :=
  portals.find? (fun q => decide (q.entrance.Contains p))

/-- Step 6: where a body at `p` with velocity `v` ends up. A portal with no exit leaves the body in
place, but its effect on velocity still applies. -/
def throughPortals (portals : List Portal) (p v : Vec3) : Vec3 × Vec3 :=
  match portalAt portals p with
  | some q => (q.exit.getD p, q.effect.apply v)
  | none => (p, v)

/-- Steps 5 to 9 for one body. -/
def moveBody (w : World) (b : Body) : Body :=
  let laws := w.laws
  let room := w.bounds.inset b.extent
  let dt := laws.timeStep * timeScaleAt w.regions b.position
  let move := moveAxis laws.topology laws.restitution dt
  let x := move room.minX room.maxX b.position.x b.velocity.x
  let y := move room.minY room.maxY b.position.y b.velocity.y
  let z := move room.minZ room.maxZ b.position.z b.velocity.z
  let landed := throughPortals w.portals ⟨x.1, y.1, z.1⟩ ⟨x.2, y.2, z.2⟩
  { b with
    position := room.clampPoint (landed.1.snap laws.grid)
    velocity := landed.2.snap laws.grid
    mass := laws.massRate * b.mass }

/-- Steps 1 and 2 for all bodies: the forces. -/
def applyForces (w : World) : List Body :=
  pairAll (forcePair w.laws) (w.bodies.map (accelerate w.laws w.regions))

/-- Advance every body by one time step. Bounds, laws, regions, portals and rules do not change. -/
def tick (w : World) : World :=
  let collided := collisionStage w.laws w.nextId (applyForces w)
  { w with
    bodies := (collided.1.map (limitSpeed w.laws)).map (moveBody w)
    tick := w.tick + 1
    nextId := collided.2 }

end Paradox

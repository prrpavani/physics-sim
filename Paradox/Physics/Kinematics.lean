import Paradox.Core.World

/-!
# One tick of the simulation

Semi-implicit Euler with component-wise clamping:

    a  = clampAbs(gravity, maxAcceleration)
    v' = clampAbs(v + dt * a, maxSpeed)
    p' = clampPoint(bounds, p + dt * v')

A body that reaches a wall is held there. Its velocity is not reflected, and collisions between
bodies are not modelled.
-/

namespace Paradox

/-- Advance one body by one time step. Only its position and velocity change. -/
def tickBody (laws : PhysicsLaws) (bounds : Bounds) (b : Body) : Body :=
  let acceleration := laws.gravity.clampAbs laws.maxAcceleration
  let velocity := (b.velocity.add (acceleration.scale laws.timeStep)).clampAbs laws.maxSpeed
  let position := bounds.clampPoint (b.position.add (velocity.scale laws.timeStep))
  { b with position, velocity }

/-- Advance every body by one time step. Bounds and laws do not change. -/
def tick (w : World) : World :=
  { w with bodies := w.bodies.map (tickBody w.laws w.bounds) }

end Paradox

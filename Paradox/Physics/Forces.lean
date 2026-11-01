import Paradox.Core.World
import Paradox.Physics.Pairwise

/-!
# Forces

External forces act on each body alone. Pair forces act between two bodies.
-/

namespace Paradox

/-- The inputs to a formula about body `a` alone. Distance is measured from the centre of space. -/
def selfInputs (a : Body) : LawInputs :=
  ⟨a.mass, 0, a.charge, 0, a.position.dot a.position, a.velocity.dot a.velocity⟩

/-- The distance between two bodies, squared, under the chosen way of measuring distance. -/
def metricSquared (m : Metric) (n : Vec3) : ℚ :=
  match m with
  | .euclidean => n.dot n
  | .manhattan => (|n.x| + |n.y| + |n.z|) * (|n.x| + |n.y| + |n.z|)
  | .chebyshev => max |n.x| (max |n.y| |n.z|) * max |n.x| (max |n.y| |n.z|)

/-- The inputs to a formula about bodies `a` and `b`. -/
def pairInputs (m : Metric) (a b : Body) : LawInputs :=
  ⟨a.mass, b.mass, a.charge, b.charge, metricSquared m (b.position.sub a.position),
   a.velocity.dot a.velocity⟩

/-- The time rate at point `p`: that of the first region containing `p`, otherwise normal time. -/
def timeScaleAt (regions : List Region) (p : Vec3) : ℚ :=
  match regions.find? (fun r => decide (r.box.Contains p)) with
  | some r => r.timeScale
  | none => 1

/-- The acceleration a body feels from everything except other bodies, before any limit: gravity,
fields, the central force, drag and the magnetic field. -/
def externalAcceleration (laws : PhysicsLaws) (b : Body) : Vec3 :=
  let i := selfInputs b
  let fromFields := laws.fields.foldl
    (fun total f => if f.region.Contains b.position then total.add f.acceleration else total)
    laws.gravity
  let fromCentral := b.position.scale (-(laws.central.eval i))
  let fromDrag := b.velocity.scale (-(laws.drag.eval i))
  let fromMagnetic := (b.velocity.cross laws.magnetic).scale (b.charge / b.mass)
  fromFields.add (fromCentral.add (fromDrag.add fromMagnetic))

/-- Add one step of external acceleration to a body's velocity. Each component is limited. -/
def accelerate (laws : PhysicsLaws) (regions : List Region) (b : Body) : Body :=
  let a := (externalAcceleration laws b).clampAbs laws.maxAcceleration
  let dt := laws.timeStep * timeScaleAt regions b.position
  { b with velocity := b.velocity.add (a.scale dt) }

/-- Apply the invented force between two bodies for one step. The force value is worked out once,
then applied to `a` and, multiplied by `reaction`, the opposite way to `b`. -/
def forcePair (laws : PhysicsLaws) (a b : Body) : Body × Body :=
  let n := b.position.sub a.position
  let f := laws.timeStep * laws.pairForce.eval (pairInputs laws.metric a b)
  ({ a with velocity := a.velocity.add (n.scale (f / a.mass)) },
   { b with velocity := b.velocity.sub (n.scale (laws.reaction * f / b.mass)) })

end Paradox

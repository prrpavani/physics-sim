import Paradox.Core.Vector

namespace Paradox

/-- The shape of a body. For contact with walls and other bodies, a cube counts as a sphere whose
radius is the cube's half-width. -/
inductive Shape where
  | sphere (radius : ℚ)
  | cube (halfWidth : ℚ)
  deriving DecidableEq, Repr

/-- How far a shape reaches from its centre. -/
def Shape.extent : Shape → ℚ
  | .sphere r => r
  | .cube h => h

/-- An object in the world. `id` names the object; `position` is its centre. -/
structure Body where
  id : Nat
  shape : Shape
  position : Vec3
  velocity : Vec3
  mass : ℚ
  /-- Electric-style charge. It only matters to laws that use it. -/
  charge : ℚ
  deriving DecidableEq, Repr

/-- How far this body reaches from its centre. -/
def Body.extent (b : Body) : ℚ :=
  b.shape.extent

end Paradox

import Paradox.Core.Vector

namespace Paradox

/-- A sphere in the world. `position` is its centre. -/
structure Body where
  id : Nat
  position : Vec3
  velocity : Vec3
  mass : ℚ
  radius : ℚ
  deriving DecidableEq, Repr

end Paradox

import Paradox.Core.Vector

namespace Paradox

/-- An object in the world. -/
structure Body where
  position : Vec3
  velocity : Vec3
  mass : ℚ
  deriving DecidableEq, Repr

end Paradox

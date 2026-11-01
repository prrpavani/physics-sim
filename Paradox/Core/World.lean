import Paradox.Core.Body
import Paradox.Core.Bounds

namespace Paradox

/-- The laws of a universe. The first six are the ones users play with. -/
structure Laws where
  /-- Acceleration along the up axis. Positive pulls up. -/
  gravity : ℚ
  /-- How strongly objects pull on each other. Negative pushes them apart. -/
  pull : ℚ
  /-- Newton's third law: an object that is pulled also pulls back. -/
  thirdLaw : Bool
  /-- Fraction of speed kept at a wall. Above 1, walls add speed. -/
  restitution : ℚ
  /-- Every velocity is multiplied by this at the end of each step. -/
  multiplier : ℚ
  /-- Enforce the speed limit once more at the end of each step. -/
  limiter : Bool
  /-- Limit on each velocity component. -/
  maxSpeed : ℚ
  /-- Length of one step. -/
  timeStep : ℚ
  /-- Values are rounded to multiples of `1 / grid`, so exact numbers stay small. 0 means no rounding. -/
  grid : Nat
  deriving DecidableEq, Repr

/-- The complete state of a universe at one moment. -/
structure World where
  bodies : List Body
  bounds : Bounds
  laws : Laws
  tick : Nat
  deriving DecidableEq, Repr

end Paradox

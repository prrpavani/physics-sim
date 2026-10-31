import Paradox.Core.Body
import Paradox.Core.Bounds

namespace Paradox

/-- The rules that every body follows. Environmental events change these. -/
structure PhysicsLaws where
  /-- Uniform acceleration applied to every body, independent of its mass. -/
  gravity : Vec3
  /-- Limit on the absolute value of each velocity component. -/
  maxSpeed : ℚ
  /-- Limit on the absolute value of each applied acceleration component. -/
  maxAcceleration : ℚ
  /-- Length of one discrete simulation step. -/
  timeStep : ℚ
  deriving DecidableEq, Repr

/-- The complete state of the simulation at one moment. -/
structure World where
  bodies : List Body
  bounds : Bounds
  laws : PhysicsLaws
  deriving DecidableEq, Repr

end Paradox

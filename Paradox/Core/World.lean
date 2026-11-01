import Paradox.Core.Body
import Paradox.Core.Bounds
import Paradox.Rules.Syntax

namespace Paradox

/-- A region of space with its own extra acceleration. Where fields overlap, their accelerations
add together. -/
structure Field where
  region : Bounds
  acceleration : Vec3
  deriving DecidableEq, Repr

/-- A named, coloured part of space where time can run at a different rate. Where regions overlap,
the first one in the list decides the time rate. -/
structure Region where
  name : String
  color : String
  box : Bounds
  /-- Time inside the region runs at this multiple of normal time. -/
  timeScale : ℚ
  deriving DecidableEq, Repr

/-- What a portal does to the velocity of a body passing through it. -/
inductive PortalEffect where
  | none
  | reverse
  /-- A quarter turn around the vertical axis. -/
  | rotate
  | scale (k : ℚ)
  deriving DecidableEq, Repr

/-- A one-way portal. A body whose centre lands in `entrance` is moved to `exit`. A portal with no
exit leaves the body in place. The consistency checks report this as missing behaviour. -/
structure Portal where
  entrance : Bounds
  exit : Option Vec3
  effect : PortalEffect
  deriving DecidableEq, Repr

/-- The shape of space. -/
inductive Topology where
  /-- Solid walls. Bodies bounce off them. -/
  | box
  /-- Space wraps around. A body leaving one side comes back on the opposite side. -/
  | torus
  deriving DecidableEq, Repr

/-- How distance is measured for force formulas. -/
inductive Metric where
  /-- Straight-line distance. -/
  | euclidean
  /-- The sum of the distances along each axis. -/
  | manhattan
  /-- The largest distance along any axis. -/
  | chebyshev
  deriving DecidableEq, Repr

/-- What happens when two bodies touch. -/
inductive CollisionMode where
  /-- They pass through each other. -/
  | none
  /-- They bounce off each other. -/
  | bounce
  /-- They swap velocities. -/
  | exchangeVelocity
  /-- They swap masses. -/
  | exchangeMass
  /-- They join into one body. -/
  | merge
  /-- They stay as they are and create one new body, up to the population limit. -/
  | spawn
  deriving DecidableEq, Repr

/-- The rules that every body follows. Environmental events change these. -/
structure PhysicsLaws where
  /-- Acceleration applied to every body, independent of its mass. -/
  gravity : Vec3
  /-- Extra acceleration in parts of the world. -/
  fields : List Field
  /-- Limit on the size of each velocity component. -/
  maxSpeed : ℚ
  /-- Limit on the size of each applied acceleration component. -/
  maxAcceleration : ℚ
  /-- Length of one discrete simulation step. -/
  timeStep : ℚ
  /-- Fraction of speed kept in a bounce: 1 keeps all of it, 0 keeps none. -/
  restitution : ℚ
  /-- The force between two bodies, as a number multiplied by the line from one body to the other.
  Positive numbers pull bodies together; negative numbers push them apart. -/
  pairForce : LawExpr
  /-- How strongly the second body feels the opposite force. 1 is Newton's third law. -/
  reaction : ℚ
  /-- Slows a body in proportion to its velocity. A negative value speeds it up. -/
  drag : LawExpr
  /-- Pulls a body toward the centre of space in proportion to its distance from the centre. -/
  central : LawExpr
  /-- A uniform magnetic field. It turns moving charged bodies. -/
  magnetic : Vec3
  /-- Every body's mass is multiplied by this each step. 1 means mass never changes. -/
  massRate : ℚ
  /-- The shape of space. -/
  topology : Topology
  /-- How distance is measured for force formulas. -/
  metric : Metric
  /-- What happens when two bodies touch. -/
  collisions : CollisionMode
  /-- The most bodies that collisions and rules may create. Events may still add more. -/
  populationLimit : Nat
  /-- Positions and velocities are rounded to multiples of `1 / grid`. 0 means no rounding. -/
  grid : Nat
  deriving DecidableEq, Repr

/-- The complete state of the simulation at one moment. -/
structure World where
  bodies : List Body
  bounds : Bounds
  laws : PhysicsLaws
  regions : List Region
  portals : List Portal
  rules : List Rule
  /-- The number of steps taken so far. -/
  tick : Nat
  /-- The id the next created body will get. -/
  nextId : Nat
  deriving DecidableEq, Repr

end Paradox

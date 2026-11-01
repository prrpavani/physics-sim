import Paradox.Core.Body
import Paradox.Core.Bounds
import Paradox.Core.LawExpr

/-!
# The rule language

Rules are data, not code. Users can only build rules from the pieces below, so every rule has a
defined meaning (`Rules/Semantics.lean`) and can be checked (`Rules/Analysis.lean`).
-/

namespace Paradox

/-- Which bodies a rule applies to. -/
inductive BodyCond where
  | all
  /-- The body's centre is inside the box. -/
  | inBox (box : Bounds)
  /-- The body's centre is inside the box and was not inside it one step earlier. -/
  | entersBox (box : Bounds)
  /-- The body's centre is inside the region with this name. -/
  | inRegion (name : String)
  /-- The body's centre is inside some region of this colour. -/
  | onColor (color : String)
  /-- Some velocity component is larger than `s` in size. -/
  | speedAbove (s : ℚ)
  | not (c : BodyCond)
  deriving DecidableEq, Repr

/-- A change made to one body. -/
inductive BodyAction where
  /-- Push the body with force `f` for one time step. Heavier bodies change speed less. -/
  | applyForce (f : Vec3)
  | reverseVelocity
  /-- Turn the velocity a quarter turn around the vertical axis. -/
  | rotateVelocity
  | scaleVelocity (k : ℚ)
  /-- Bring the velocity back within the current speed limit. -/
  | clampVelocity
  | translate (d : Vec3)
  /-- Bring the body back fully inside the world. -/
  | clampPosition
  | scaleMass (k : ℚ)
  /-- Set the body's mass from a formula, such as one that grows with speed. -/
  | setMassFormula (f : LawExpr)
  | setCharge (q : ℚ)
  deriving DecidableEq, Repr

/-- A condition on the whole world. -/
inductive WorldCond where
  | always
  /-- The size of gravity is greater than `g`. -/
  | gravityAbove (g : ℚ)
  /-- Gravity is different from what it was one step earlier. -/
  | gravityChanged
  /-- The step count is a multiple of `n`. -/
  | everyTicks (n : Nat)
  | not (c : WorldCond)
  deriving DecidableEq, Repr

/-- A change made to the laws of the world. -/
inductive WorldAction where
  | setGravity (g : Vec3)
  | reverseGravity
  | setMaxSpeed (v : ℚ)
  | setPairForce (f : LawExpr)
  | setReaction (r : ℚ)
  | setMassRate (r : ℚ)
  deriving DecidableEq, Repr

/-- A rule. Rules run at the end of every step, after the bodies have moved. -/
inductive Rule where
  /-- Do nothing. -/
  | skip
  /-- Change every body that meets the condition. -/
  | body (c : BodyCond) (a : BodyAction)
  | world (a : WorldAction)
  /-- Remove every body that meets the condition. -/
  | destroy (c : BodyCond)
  /-- Add a copy of this body, with a new id, if it is valid in the world at that moment and the
  population limit allows it. Otherwise nothing happens. -/
  | create (template : Body)
  /-- Run `a`, then `b`. -/
  | seq (a b : Rule)
  /-- Run `r` only if the condition is true. -/
  | when (c : WorldCond) (r : Rule)
  deriving DecidableEq, Repr

end Paradox

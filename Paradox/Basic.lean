/-!
# The parts of a universe

A world is a grid of whole-number cells. Bodies sit on cells and move a whole number of cells
per tick. Using whole numbers, not decimals, means every calculation is exact: there is no
rounding for a proof to worry about.
-/

namespace Paradox

/-- A point on the grid, or a velocity in cells per tick. -/
structure Vec2 where
  x : Int
  y : Int
  deriving Repr, DecidableEq, Inhabited

instance : Add Vec2 := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩

@[simp] theorem Vec2.add_x (a b : Vec2) : (a + b).x = a.x + b.x := rfl
@[simp] theorem Vec2.add_y (a b : Vec2) : (a + b).y = a.y + b.y := rfl

/-- A ball in the world. `id` names it; no two bodies in a safe world share an `id`. -/
structure Body where
  id : Nat
  pos : Vec2
  vel : Vec2
  mass : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A one-way portal. A body that lands on `entrance` is moved to `exit`. -/
structure Portal where
  entrance : Vec2
  exit : Vec2
  deriving Repr, DecidableEq, Inhabited

/-- Everything about a universe at one moment: its size, its laws, and what is in it.
Cells run from `0` to `width - 1` across and `0` to `height - 1` down. -/
structure World where
  width : Nat
  height : Nat
  /-- The fastest a body may move along either axis, in cells per tick. -/
  maxSpeed : Nat
  /-- Added to every body's velocity once per tick. -/
  gravity : Vec2
  bodies : List Body
  portals : List Portal
  tick : Nat
  deriving Repr, Inhabited

/-- Something that can happen to a world. The engine may reject an event; see `step`. -/
inductive Event where
  /-- One tick of time: gravity acts, then every body moves. -/
  | move
  /-- Gravity changes to any value. Speed limits still hold, because velocities are capped. -/
  | changeGravity (g : Vec2)
  | spawnBody (b : Body)
  | removeBody (id : Nat)
  /-- A push that adds `dv` to one body's velocity, capped at the speed limit. -/
  | applyImpulse (id : Nat) (dv : Vec2)
  | addPortal (p : Portal)
  /-- Two touching bodies of equal mass collide and swap velocities. -/
  | collide (a b : Nat)
  deriving Repr, Inhabited

end Paradox

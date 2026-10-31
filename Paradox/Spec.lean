import Paradox.Basic

/-!
# What "safe" means

These definitions are what the main theorems promise. Read them before trusting a proof.
-/

namespace Paradox

/-- The point is on the grid. -/
def InBounds (w : World) (p : Vec2) : Prop :=
  0 ≤ p.x ∧ p.x < w.width ∧ 0 ≤ p.y ∧ p.y < w.height

/-- The velocity is within the speed limit along both axes. -/
def SpeedOk (w : World) (v : Vec2) : Prop :=
  -(w.maxSpeed : Int) ≤ v.x ∧ v.x ≤ w.maxSpeed ∧ -(w.maxSpeed : Int) ≤ v.y ∧ v.y ≤ w.maxSpeed

/-- A body is on the grid, within the speed limit, and has positive mass. -/
def ValidBody (w : World) (b : Body) : Prop :=
  InBounds w b.pos ∧ SpeedOk w b.vel ∧ 0 < b.mass

/-- A safe world:
1. The speed limit is smaller than the world, so one bounce off a wall always lands inside.
2. Every body is valid.
3. No two bodies share an id.
4. Both ends of every portal are on the grid. -/
def SafeWorld (w : World) : Prop :=
  w.maxSpeed < w.width ∧ w.maxSpeed < w.height ∧
  (∀ b ∈ w.bodies, ValidBody w b) ∧
  (w.bodies.map Body.id).Nodup ∧
  (∀ p ∈ w.portals, InBounds w p.entrance ∧ InBounds w p.exit)

/-- Every body is on the grid. -/
def WithinBounds (w : World) : Prop := ∀ b ∈ w.bodies, InBounds w b.pos

/-- Every body is within the speed limit. -/
def SpeedBounded (w : World) : Prop := ∀ b ∈ w.bodies, SpeedOk w b.vel

/-- The total momentum of a list of bodies: the sum of mass times velocity. -/
def totalMomentum (bs : List Body) : Vec2 :=
  ⟨(bs.map fun b => (b.mass : Int) * b.vel.x).sum, (bs.map fun b => (b.mass : Int) * b.vel.y).sum⟩

instance (w : World) (p : Vec2) : Decidable (InBounds w p) := by unfold InBounds; infer_instance
instance (w : World) (v : Vec2) : Decidable (SpeedOk w v) := by unfold SpeedOk; infer_instance
instance (w : World) (b : Body) : Decidable (ValidBody w b) := by unfold ValidBody; infer_instance
instance (w : World) : Decidable (SafeWorld w) := by unfold SafeWorld; infer_instance

end Paradox

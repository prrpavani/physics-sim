import Paradox.Core.World
import Paradox.Invariants.Environment
import Paradox.Invariants.Speed

/-!
# What rules do

`prev` is the world one step earlier. `entersBox` and `gravityChanged` look at it.
-/

namespace Paradox

/-- The inputs to a formula about one body, as seen by a rule. -/
def ruleInputs (b : Body) : LawInputs :=
  ⟨b.mass, 0, b.charge, 0, b.position.dot b.position, b.velocity.dot b.velocity⟩

/-- Whether a body meets the condition. -/
def BodyCond.test (prev : World) : BodyCond → Body → Bool
  | .all, _ => true
  | .inBox box, b => decide (box.Contains b.position)
  | .entersBox box, b =>
    decide (box.Contains b.position) &&
      match prev.bodies.find? (fun old => old.id == b.id) with
      | some old => !decide (box.Contains old.position)
      | none => true
  | .inRegion name, b =>
    prev.regions.any fun r => r.name == name && decide (r.box.Contains b.position)
  | .onColor color, b =>
    prev.regions.any fun r => r.color == color && decide (r.box.Contains b.position)
  | .speedAbove s, b =>
    decide (s < |b.velocity.x|) || decide (s < |b.velocity.y|) || decide (s < |b.velocity.z|)
  | .not c, b => !(c.test prev b)

/-- The body after the action. -/
def BodyAction.apply (w : World) : BodyAction → Body → Body
  | .applyForce f, b =>
    { b with velocity := b.velocity.add (f.scale (w.laws.timeStep / b.mass)) }
  | .reverseVelocity, b => { b with velocity := b.velocity.neg }
  | .rotateVelocity, b => { b with velocity := ⟨b.velocity.z, b.velocity.y, -b.velocity.x⟩ }
  | .scaleVelocity k, b => { b with velocity := b.velocity.scale k }
  | .clampVelocity, b => { b with velocity := b.velocity.clampAbs w.laws.maxSpeed }
  | .translate d, b => { b with position := b.position.add d }
  | .clampPosition, b => { b with position := (w.bounds.inset b.extent).clampPoint b.position }
  | .scaleMass k, b => { b with mass := k * b.mass }
  | .setMassFormula f, b => { b with mass := f.eval (ruleInputs b) }
  | .setCharge q, b => { b with charge := q }

/-- Whether the world meets the condition. -/
def WorldCond.test (prev w : World) : WorldCond → Bool
  | .always => true
  | .gravityAbove g =>
    decide (g < 0) || decide (g * g < w.laws.gravity.dot w.laws.gravity)
  | .gravityChanged => decide (prev.laws.gravity ≠ w.laws.gravity)
  | .everyTicks n => n != 0 && w.tick % n == 0
  | .not c => !(c.test prev w)

/-- The laws after the action. -/
def WorldAction.apply : WorldAction → PhysicsLaws → PhysicsLaws
  | .setGravity g, l => { l with gravity := g }
  | .reverseGravity, l => { l with gravity := l.gravity.neg }
  | .setMaxSpeed v, l => { l with maxSpeed := v }
  | .setPairForce f, l => { l with pairForce := f }
  | .setReaction r, l => { l with reaction := r }
  | .setMassRate r, l => { l with massRate := r }

/-- A body created by a rule is valid in this world: it fits, is inside, is within the speed limit,
and has positive mass. -/
def CanCreate (w : World) (t : Body) : Prop :=
  FitsIn w.bounds t ∧
  0 < t.mass ∧
  (w.bounds.inset t.extent).Contains t.position ∧
  t.velocity.WithinAbs w.laws.maxSpeed ∧
  w.bodies.length < w.laws.populationLimit

instance (w : World) (t : Body) : Decidable (CanCreate w t) := by unfold CanCreate; infer_instance

/-- The world after running a rule. -/
def Rule.eval (prev : World) : Rule → World → World
  | .skip, w => w
  | .body c a, w =>
    { w with bodies := w.bodies.map fun b => if c.test prev b then a.apply w b else b }
  | .world a, w => { w with laws := a.apply w.laws }
  | .destroy c, w => { w with bodies := w.bodies.filter fun b => !c.test prev b }
  | .create t, w =>
    if CanCreate w t then
      { w with bodies := w.bodies ++ [{ t with id := w.nextId }], nextId := w.nextId + 1 }
    else w
  | .seq a b, w => b.eval prev (a.eval prev w)
  | .when c r, w => if c.test prev w then r.eval prev w else w

/-- The world after running a list of rules in order. -/
def evalRules (prev : World) (rules : List Rule) (w : World) : World :=
  rules.foldl (fun current r => r.eval prev current) w

end Paradox

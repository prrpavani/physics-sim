import Paradox.Physics.Kinematics
import Paradox.Rules.Semantics
import Paradox.Rules.Analysis

/-!
# Environmental events and the transition function

Events form a closed type, so every event has defined meaning and can be sent as data. One step
applies the event, advances time, then runs the world's rules:

    step w e = evalRules w rules (tick (applyEvent w e))
-/

namespace Paradox

/-- The complete list of ways the environment can change. -/
inductive EnvironmentEvent where
  /-- No environmental change; time still advances. -/
  | idle
  | changeGravity (g : Vec3)
  | reverseGravity
  | disableGravity
  | changeMaxSpeed (v : ℚ)
  | changeMaxAcceleration (a : ℚ)
  | changeRestitution (e : ℚ)
  | changeTimeStep (dt : ℚ)
  | changeBounds (b : Bounds)
  | addField (f : Field)
  | clearFields
  /-- Replace the force between bodies with a new formula. -/
  | setPairForce (f : LawExpr)
  /-- Change how strongly bodies feel the opposite force. 1 is Newton's third law. -/
  | setReaction (r : ℚ)
  | setDrag (f : LawExpr)
  | setCentral (f : LawExpr)
  | setMagnetic (b : Vec3)
  | setMassRate (r : ℚ)
  | setTopology (t : Topology)
  | setMetric (m : Metric)
  | setCollisions (mode : CollisionMode)
  | setPopulationLimit (n : Nat)
  | setGrid (n : Nat)
  /-- Reverse the velocity of every body. -/
  | reverseTime
  | spawnBody (b : Body)
  | removeBody (id : Nat)
  /-- Add `dv` to one body's velocity. -/
  | applyImpulse (id : Nat) (dv : Vec3)
  /-- Set one body's position and velocity directly. -/
  | setBodyState (id : Nat) (p v : Vec3)
  | addRegion (r : Region)
  | clearRegions
  | addPortal (p : Portal)
  | clearPortals
  | addRule (r : Rule)
  | clearRules
  deriving DecidableEq, Repr

/-- Change the laws only. -/
def withLaws (w : World) (f : PhysicsLaws → PhysicsLaws) : World :=
  { w with laws := f w.laws }

/-- Change the bodies with this id. -/
def updateBody (id : Nat) (f : Body → Body) (bs : List Body) : List Body :=
  bs.map fun b => if b.id = id then f b else b

/-- Change the world according to the event. Bodies do not move yet. -/
def applyEvent (w : World) : EnvironmentEvent → World
  | .idle => w
  | .changeGravity g => withLaws w fun l => { l with gravity := g }
  | .reverseGravity => withLaws w fun l => { l with gravity := l.gravity.neg }
  | .disableGravity => withLaws w fun l => { l with gravity := Vec3.zero }
  | .changeMaxSpeed v => withLaws w fun l => { l with maxSpeed := v }
  | .changeMaxAcceleration a => withLaws w fun l => { l with maxAcceleration := a }
  | .changeRestitution e => withLaws w fun l => { l with restitution := e }
  | .changeTimeStep dt => withLaws w fun l => { l with timeStep := dt }
  | .changeBounds b => { w with bounds := b }
  | .addField f => withLaws w fun l => { l with fields := l.fields ++ [f] }
  | .clearFields => withLaws w fun l => { l with fields := [] }
  | .setPairForce f => withLaws w fun l => { l with pairForce := f }
  | .setReaction r => withLaws w fun l => { l with reaction := r }
  | .setDrag f => withLaws w fun l => { l with drag := f }
  | .setCentral f => withLaws w fun l => { l with central := f }
  | .setMagnetic b => withLaws w fun l => { l with magnetic := b }
  | .setMassRate r => withLaws w fun l => { l with massRate := r }
  | .setTopology t => withLaws w fun l => { l with topology := t }
  | .setMetric m => withLaws w fun l => { l with metric := m }
  | .setCollisions mode => withLaws w fun l => { l with collisions := mode }
  | .setPopulationLimit n => withLaws w fun l => { l with populationLimit := n }
  | .setGrid n => withLaws w fun l => { l with grid := n }
  | .reverseTime => { w with bodies := w.bodies.map fun b => { b with velocity := b.velocity.neg } }
  | .spawnBody b => { w with bodies := w.bodies ++ [b], nextId := max w.nextId (b.id + 1) }
  | .removeBody id => { w with bodies := w.bodies.filter fun b => b.id ≠ id }
  | .applyImpulse id dv =>
    { w with bodies := updateBody id (fun b => { b with velocity := b.velocity.add dv }) w.bodies }
  | .setBodyState id p v =>
    { w with bodies := updateBody id (fun b => { b with position := p, velocity := v }) w.bodies }
  | .addRegion r => { w with regions := w.regions ++ [r] }
  | .clearRegions => { w with regions := [] }
  | .addPortal p => { w with portals := w.portals ++ [p] }
  | .clearPortals => { w with portals := [] }
  | .addRule r => { w with rules := w.rules ++ [r] }
  | .clearRules => { w with rules := [] }

/-- The transition function `T(S, event)`: apply the event, advance time, run the rules. -/
def step (w : World) (e : EnvironmentEvent) : World :=
  let moved := tick (applyEvent w e)
  evalRules w moved.rules moved

/-- Run a finite sequence of events in order. -/
def run (w : World) (events : List EnvironmentEvent) : World :=
  events.foldl step w

/-- A new body is well-formed and does not break any guarantee. -/
def BodyAllowed (w : World) (b : Body) : Prop :=
  FitsIn w.bounds b ∧
  0 < b.mass ∧
  b.id ∉ w.bodies.map Body.id ∧
  (w.bounds.inset b.extent).Contains b.position ∧
  b.velocity.WithinAbs w.laws.maxSpeed

instance (w : World) (b : Body) : Decidable (BodyAllowed w b) := by
  unfold BodyAllowed; infer_instance

/-- Events permitted in a protected universe. Any force formula, gravity, field or topology is
allowed, because every guarantee holds for all of them. Limits must be meaningful, new bodies must
be valid, and new rules must pass the rule check. -/
def Allowed (w : World) : EnvironmentEvent → Prop
  | .changeMaxSpeed v => 0 < v
  | .changeMaxAcceleration a => 0 ≤ a
  | .changeRestitution e => 0 ≤ e ∧ e ≤ 1
  | .changeTimeStep dt => 0 < dt
  | .changeBounds b => b.Valid ∧ ∀ body ∈ w.bodies, FitsIn b body
  | .setMassRate r => 0 < r
  | .spawnBody b => BodyAllowed w b
  | .addRegion r => 0 ≤ r.timeScale
  | .addPortal p => p.effect.Safe
  | .addRule r => r.certified = true
  | _ => True

instance (w : World) (e : EnvironmentEvent) : Decidable (Allowed w e) := by
  cases e <;> unfold Allowed <;> infer_instance

end Paradox

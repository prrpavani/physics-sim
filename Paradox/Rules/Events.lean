import Paradox.Physics.Kinematics

/-!
# Environmental events and the transition function

Events form a closed type, so every event has defined semantics and can be serialized as data.
The transition function is `step w e = tick (applyEvent w e)`: the event changes the laws, and the
new laws take effect in the same step.
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
  | changeRestitution (r : ℚ)
  deriving DecidableEq, Repr

namespace EnvironmentEvent

/-- The laws after this event. -/
def applyToLaws : EnvironmentEvent → PhysicsLaws → PhysicsLaws
  | idle, l => l
  | changeGravity g, l => { l with gravity := g }
  | reverseGravity, l => { l with gravity := l.gravity.neg }
  | disableGravity, l => { l with gravity := Vec3.zero }
  | changeMaxSpeed v, l => { l with maxSpeed := v }
  | changeMaxAcceleration a, l => { l with maxAcceleration := a }
  | changeRestitution r, l => { l with restitution := r }

end EnvironmentEvent

/-- Change the world's laws according to the event. Bodies do not move yet. -/
def applyEvent (w : World) (e : EnvironmentEvent) : World :=
  { w with laws := e.applyToLaws w.laws }

/-- The transition function `T(S, event)`. -/
def step (w : World) (e : EnvironmentEvent) : World :=
  tick (applyEvent w e)

/-- Run a finite sequence of events in order. -/
def run (w : World) (events : List EnvironmentEvent) : World :=
  events.foldl step w

/-- Events permitted in a protected universe: new limits must be physically meaningful. -/
def Allowed (_w : World) : EnvironmentEvent → Prop
  | .changeMaxSpeed v => 0 < v
  | .changeMaxAcceleration a => 0 ≤ a
  | .changeRestitution r => 0 ≤ r ∧ r ≤ 1
  | _ => True

instance (w : World) (e : EnvironmentEvent) : Decidable (Allowed w e) := by
  cases e <;> unfold Allowed <;> infer_instance

end Paradox

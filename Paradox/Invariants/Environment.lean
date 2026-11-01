import Paradox.Core.World

namespace Paradox

/-- A body's size is not negative and it fits inside the box. -/
def FitsIn (bounds : Bounds) (b : Body) : Prop :=
  0 ≤ b.extent ∧ (bounds.inset b.extent).Valid

instance (bounds : Bounds) (b : Body) : Decidable (FitsIn bounds b) := by
  unfold FitsIn; infer_instance

/-- A portal cannot make a body faster along any axis. -/
def PortalEffect.Safe : PortalEffect → Prop
  | .scale k => |k| ≤ 1
  | _ => True

instance (e : PortalEffect) : Decidable e.Safe := by cases e <;> unfold PortalEffect.Safe <;> infer_instance

/-- The laws are physically meaningful, and every body fits inside the world. -/
def SafeEnvironment (w : World) : Prop :=
  w.bounds.Valid ∧
  0 < w.laws.maxSpeed ∧
  0 ≤ w.laws.maxAcceleration ∧
  0 < w.laws.timeStep ∧
  (0 ≤ w.laws.restitution ∧ w.laws.restitution ≤ 1) ∧
  0 < w.laws.massRate ∧
  (∀ p ∈ w.portals, p.effect.Safe) ∧
  (∀ r ∈ w.regions, 0 ≤ r.timeScale) ∧
  ∀ b ∈ w.bodies, FitsIn w.bounds b

instance (w : World) : Decidable (SafeEnvironment w) := by unfold SafeEnvironment; infer_instance

end Paradox

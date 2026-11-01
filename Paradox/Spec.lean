import Paradox.Physics.Kinematics

/-!
# The four promises

These definitions say what PARADOX claims. Read them before trusting a proof.
-/

namespace Paradox

/-! ## A well-formed universe -/

/-- The laws are meaningful: a positive speed limit and time step, and a bounciness that is not
negative. -/
def LawsOk (l : Laws) : Prop :=
  0 < l.maxSpeed ∧ 0 < l.timeStep ∧ 0 ≤ l.restitution

/-- An object has positive mass and fits inside the world. -/
def BodyOk (bounds : Bounds) (b : Body) : Prop :=
  0 < b.mass ∧ (bounds.inset b.radius).Valid

/-- The laws are meaningful, and every object is valid. -/
def WellFormed (w : World) : Prop :=
  LawsOk w.laws ∧ ∀ b ∈ w.bodies, BodyOk w.bounds b

/-! ## Promise 1: objects stay inside -/

/-- Every object is fully inside the world. -/
def StaysInside (w : World) : Prop :=
  ∀ b ∈ w.bodies, (w.bounds.inset b.radius).Contains b.position

/-! ## Promise 2: the speed limit -/

/-- Every velocity component is within the speed limit. -/
def WithinSpeedLimit (w : World) : Prop :=
  ∀ b ∈ w.bodies, b.velocity.WithinAbs w.laws.maxSpeed

/-- The laws that keep the speed limit: the limiter is on, or neither walls nor the multiplier can add
speed. -/
def SpeedSafe (l : Laws) : Prop :=
  l.limiter = true ∨ (l.restitution ≤ 1 ∧ |l.multiplier| ≤ 1)

/-! ## Promise 3: momentum between objects -/

/-- The total momentum of a list of objects along direction `c`. -/
def totalMomentum (c : Vec3) (bs : List Body) : ℚ :=
  (bs.map fun b => b.mass * b.velocity.dot c).sum

/-- The pull between objects does not change their total momentum along any axis. -/
def MomentumKept (w : World) : Prop :=
  ∀ c ∈ [Vec3.mk 1 0 0, Vec3.mk 0 1 0, Vec3.mk 0 0 1],
    totalMomentum c (pullStage w.laws w.bodies) = totalMomentum c w.bodies

/-- The laws that keep momentum: Newton's third law is on, or there is no pull. -/
def MomentumSafe (l : Laws) : Prop :=
  l.thirdLaw = true ∨ l.pull = 0

/-! ## Promise 4: energy never rises -/

/-- The total kinetic energy of a list of objects. -/
def totalEnergy (bs : List Body) : ℚ :=
  (bs.map fun b => b.mass * b.velocity.dot b.velocity / 2).sum

/-- The laws that keep energy from rising: nothing pushes, and nothing adds speed. -/
def EnergySafe (l : Laws) : Prop :=
  l.gravity = 0 ∧ l.pull = 0 ∧ l.restitution ≤ 1 ∧ |l.multiplier| ≤ 1

/-! ## Deciding these on a concrete world -/

instance (b : Bounds) (p : Vec3) : Decidable (b.Contains p) := by unfold Bounds.Contains; infer_instance
instance (b : Bounds) : Decidable b.Valid := by unfold Bounds.Valid; infer_instance
instance (a : Vec3) (m : ℚ) : Decidable (a.WithinAbs m) := by unfold Vec3.WithinAbs; infer_instance
instance (l : Laws) : Decidable (LawsOk l) := by unfold LawsOk; infer_instance
instance (bs : Bounds) (b : Body) : Decidable (BodyOk bs b) := by unfold BodyOk; infer_instance
instance (w : World) : Decidable (WellFormed w) := by unfold WellFormed; infer_instance
instance (w : World) : Decidable (StaysInside w) := by unfold StaysInside; infer_instance
instance (w : World) : Decidable (WithinSpeedLimit w) := by unfold WithinSpeedLimit; infer_instance
instance (l : Laws) : Decidable (SpeedSafe l) := by unfold SpeedSafe; infer_instance
instance (w : World) : Decidable (MomentumKept w) := by unfold MomentumKept; infer_instance
instance (l : Laws) : Decidable (MomentumSafe l) := by unfold MomentumSafe; infer_instance
instance (l : Laws) : Decidable (EnergySafe l) := by unfold EnergySafe; infer_instance

end Paradox

import Paradox.Verification.Verdict
import Paradox.Verification.Reference

/-!
# Conservation audit

For the laws a user has chosen, which conservation laws hold? Each answer is a theorem whose
conditions were checked on this universe, a checked counterexample, or unknown.
-/

namespace Paradox

open Engine

/-! ## Momentum in the interaction stage -/

/-- Collision modes that keep momentum. -/
def CollisionMode.KeepsMomentum : CollisionMode → Prop
  | .none | .bounce | .merge => True
  | _ => False

instance (m : CollisionMode) : Decidable m.KeepsMomentum := by
  cases m <;> unfold CollisionMode.KeepsMomentum <;> infer_instance

/-- **Bodies cannot change their total momentum by acting on each other.** With Newton's third law
on and a collision mode that keeps momentum, the pair force and collision stages keep total
momentum along any direction, whatever the force formula is. -/
theorem interaction_conserves_momentum (laws : PhysicsLaws) (hr : laws.reaction = 1)
    (hm : laws.collisions.KeepsMomentum) (c : Vec3) (nextId : Nat) (l : List Body)
    (hl : ∀ x ∈ l, 0 < x.mass) :
    totalMomentum c (collisionStage laws nextId (pairAll (forcePair laws) l)).1 =
      totalMomentum c l := by
  have hforced := pairForces_conserve_momentum laws hr c l hl
  have hpos : ∀ x ∈ pairAll (forcePair laws) l, 0 < x.mass :=
    pairAll_forall (Q := fun x => 0 < x.mass) (fun _ _ ha hb => ⟨ha, hb⟩) l hl
  unfold collisionStage
  split
  · exact hforced
  · exact (bounces_conserve_momentum _ c _ hpos).trans hforced
  · next heq => rw [heq] at hm; exact hm.elim
  · next heq => rw [heq] at hm; exact hm.elim
  · exact (merges_conserve_momentum c _ hpos).trans hforced
  · next heq => rw [heq] at hm; exact hm.elim

/-! ## Energy when nothing pushes from outside -/

/-- Nothing adds energy from outside: no gravity, fields, central force, drag or magnetism, and no
force between bodies. -/
def PhysicsLaws.NoForces (l : PhysicsLaws) : Prop :=
  l.gravity = Vec3.zero ∧ l.fields = [] ∧ l.central = .const 0 ∧ l.drag = .const 0 ∧
  l.magnetic = Vec3.zero ∧ l.pairForce = .const 0

instance (l : PhysicsLaws) : Decidable l.NoForces := by unfold PhysicsLaws.NoForces; infer_instance

theorem clampAbs_zero {m : ℚ} (hm : 0 ≤ m) : clampAbs 0 m = 0 :=
  clamp_of_mem (by linarith) hm

theorem accelerate_of_noForces {laws : PhysicsLaws} (h : laws.NoForces)
    (hm : 0 ≤ laws.maxAcceleration) (regions : List Region) (b : Body) :
    accelerate laws regions b = b := by
  obtain ⟨hg, hf, hc, hd, hb, -⟩ := h
  have hzero : externalAcceleration laws b = Vec3.zero := by
    simp [externalAcceleration, hg, hf, hc, hd, hb, Vec3.add, Vec3.scale, Vec3.cross, Vec3.zero,
      LawExpr.eval]
  simp [accelerate, hzero, Vec3.zero, Vec3.clampAbs, clampAbs_zero hm, Vec3.scale, Vec3.add]

theorem forcePair_of_noForces {laws : PhysicsLaws} (h : laws.NoForces) (a b : Body) :
    forcePair laws a b = (a, b) := by
  have hp := h.2.2.2.2.2
  simp [forcePair, hp, LawExpr.eval, Vec3.add, Vec3.sub, Vec3.scale]

theorem pairOne_identity {f : Body → Body → Body × Body} (hf : ∀ a b, f a b = (a, b))
    (l : List Body) (a : Body) : pairOne f a l = (a, l) := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [pairOne, hf, ih]

theorem pairAll_identity {f : Body → Body → Body × Body} (hf : ∀ a b, f a b = (a, b))
    (l : List Body) : pairAll f l = l := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [pairAll, ih, pairOne_identity hf]

/-- With no forces, the force stages change nothing. -/
theorem applyForces_of_noForces {w : World} (h : w.laws.NoForces) (hm : 0 ≤ w.laws.maxAcceleration) :
    applyForces w = w.bodies := by
  unfold applyForces
  rw [pairAll_identity (forcePair_of_noForces h)]
  simp [funext (accelerate_of_noForces h hm w.regions)]

theorem abs_clampAbs_le_abs (x : ℚ) {m : ℚ} (hm : 0 ≤ m) : |clampAbs x m| ≤ |x| := by
  by_cases h : |x| ≤ m
  · rw [show clampAbs x m = x from clamp_of_mem (abs_le.mp h).1 (abs_le.mp h).2]
  · exact (abs_clampAbs_le x hm).trans (not_le.mp h).le

theorem mul_self_le_of_abs_le {a b : ℚ} (h : |a| ≤ |b|) : a * a ≤ b * b := by
    rw [← abs_mul_abs_self a, ← abs_mul_abs_self b]
    exact mul_self_le_mul_self (abs_nonneg a) h

theorem dot_self_le {a b : Vec3} (hx : |a.x| ≤ |b.x|) (hy : |a.y| ≤ |b.y|) (hz : |a.z| ≤ |b.z|) :
    a.dot a ≤ b.dot b := by
  have h1 := mul_self_le_of_abs_le hx
  have h2 := mul_self_le_of_abs_le hy
  have h3 := mul_self_le_of_abs_le hz
  simp only [Vec3.dot]
  linarith

theorem effect_dot_le {e : PortalEffect} (he : e.Safe) (v : Vec3) :
    (e.apply v).dot (e.apply v) ≤ v.dot v := by
  cases e with
  | none => exact le_rfl
  | reverse => simp [PortalEffect.apply, Vec3.neg, Vec3.dot]
  | rotate =>
    simp only [PortalEffect.apply, Vec3.dot]
    nlinarith
  | scale k =>
    have hk : |k| ≤ 1 := he
    have key : ∀ x : ℚ, |k * x| ≤ |x| := fun x => by
      rw [abs_mul]; nlinarith [abs_nonneg x]
    exact dot_self_le (key _) (key _) (key _)

theorem throughPortals_dot_le {portals : List Portal} (hp : ∀ q ∈ portals, q.effect.Safe)
    (p v : Vec3) : (throughPortals portals p v).2.dot (throughPortals portals p v).2 ≤ v.dot v := by
  unfold throughPortals
  split
  next q hq => exact effect_dot_le (hp q (List.mem_of_find?_eq_some hq)) v
  next => exact le_rfl

/-- Moving a body never adds kinetic energy, if bounces, portals and the mass rate cannot. -/
theorem moveBody_energy {w : World} {b : Body} (hb : 0 < b.mass)
    (h0 : 0 ≤ w.laws.restitution) (h1 : w.laws.restitution ≤ 1)
    (hr1 : w.laws.massRate ≤ 1)
    (hp : ∀ q ∈ w.portals, q.effect.Safe) : kineticEnergy (moveBody w b) ≤ kineticEnergy b := by
  have hdot : (moveBody w b).velocity.dot (moveBody w b).velocity ≤ b.velocity.dot b.velocity := by
    unfold moveBody
    dsimp only
    refine le_trans (dot_self_le (abs_snap_le _ _) (abs_snap_le _ _) (abs_snap_le _ _)) ?_
    refine (throughPortals_dot_le hp _ _).trans ?_
    exact dot_self_le (abs_moveAxis_snd_le _ _ _ _ _ _ h0 h1)
      (abs_moveAxis_snd_le _ _ _ _ _ _ h0 h1) (abs_moveAxis_snd_le _ _ _ _ _ _ h0 h1)
  have hnn : 0 ≤ (moveBody w b).velocity.dot (moveBody w b).velocity := by
    simp only [Vec3.dot]
    nlinarith [mul_self_nonneg (moveBody w b).velocity.x, mul_self_nonneg (moveBody w b).velocity.y,
      mul_self_nonneg (moveBody w b).velocity.z]
  have hmass : (moveBody w b).mass = w.laws.massRate * b.mass := rfl
  unfold kineticEnergy
  rw [hmass]
  have hm : w.laws.massRate * b.mass ≤ b.mass := by nlinarith
  have hstep : w.laws.massRate * b.mass * (moveBody w b).velocity.dot (moveBody w b).velocity ≤
      b.mass * b.velocity.dot b.velocity := by
    calc _ ≤ b.mass * (moveBody w b).velocity.dot (moveBody w b).velocity :=
          mul_le_mul_of_nonneg_right hm hnn
      _ ≤ _ := mul_le_mul_of_nonneg_left hdot hb.le
  linarith

theorem limitSpeed_energy (laws : PhysicsLaws) (hm : 0 ≤ laws.maxSpeed) (b : Body)
    (hb : 0 < b.mass) : kineticEnergy (limitSpeed laws b) ≤ kineticEnergy b := by
  have h := dot_self_le (a := (limitSpeed laws b).velocity) (b := b.velocity)
    (abs_clampAbs_le_abs _ hm) (abs_clampAbs_le_abs _ hm) (abs_clampAbs_le_abs _ hm)
  have : b.mass * (limitSpeed laws b).velocity.dot (limitSpeed laws b).velocity ≤
      b.mass * b.velocity.dot b.velocity := mul_le_mul_of_nonneg_left h hb.le
  show b.mass * _ / 2 ≤ b.mass * _ / 2
  linarith

theorem total_map_le {Q : Body → ℚ} {f : Body → Body} (l : List Body) (G : Body → Prop)
    (hl : ∀ x ∈ l, G x) (hf : ∀ b, G b → Q (f b) ≤ Q b) : total Q (l.map f) ≤ total Q l := by
  induction l with
  | nil => exact le_rfl
  | cons b bs ih =>
    have h1 := hf b (hl b List.mem_cons_self)
    have h2 := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    simp only [total, List.map_cons, List.sum_cons] at h2 ⊢
    linarith

/-- **With no forces, energy can only fall.** In a safe environment with no forces, mass rate at most
1, and collisions that only bounce or pass through, a tick never adds total kinetic energy, however
bodies hit walls, each other or portals. -/
theorem tick_energy_le {w : World} (hf : w.laws.NoForces)
    (hc : w.laws.collisions = .none ∨ w.laws.collisions = .bounce)
    (he : SafeEnvironment w) (hpos : PositiveMass w) (hr1 : w.laws.massRate ≤ 1) :
    totalEnergy (tick w).bodies ≤ totalEnergy w.bodies := by
  obtain ⟨-, hs, ha, -, ⟨h0, h1⟩, -, hp, -, -⟩ := he
  have hforces := applyForces_of_noForces hf ha
  have hstage : ∀ x ∈ (collisionStage w.laws w.nextId (applyForces w)).1, 0 < x.mass :=
    forces_collisions_forall positiveMass_stageClosed w hpos
  have hcoll : totalEnergy (collisionStage w.laws w.nextId (applyForces w)).1 ≤
      totalEnergy w.bodies := by
    rw [hforces]
    rcases hc with hc | hc
    · simp only [collisionStage, hc]
      exact le_rfl
    · simp only [collisionStage, hc]
      exact bounces_energy h0 h1 _ hpos
  have hlimit : totalEnergy ((collisionStage w.laws w.nextId (applyForces w)).1.map
      (limitSpeed w.laws)) ≤ totalEnergy (collisionStage w.laws w.nextId (applyForces w)).1 :=
    total_map_le _ (fun x => 0 < x.mass) hstage fun b hb => limitSpeed_energy _ hs.le b hb
  have hlimitPos : ∀ x ∈ (collisionStage w.laws w.nextId (applyForces w)).1.map
      (limitSpeed w.laws), 0 < x.mass := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact hstage b hb
  have hmove : totalEnergy (((collisionStage w.laws w.nextId (applyForces w)).1.map
      (limitSpeed w.laws)).map (moveBody w)) ≤
      totalEnergy ((collisionStage w.laws w.nextId (applyForces w)).1.map (limitSpeed w.laws)) :=
    total_map_le _ (fun x => 0 < x.mass) hlimitPos fun b hb => moveBody_energy hb h0 h1 hr1 hp
  exact hmove.trans (hlimit.trans hcoll)

/-! ## Over many ticks with no events -/

/-- A world with no rules: one idle step is exactly one tick. -/
theorem step_idle_of_no_rules {w : World} (h : w.rules = []) : step w .idle = tick w := by
  have hr : (tick w).rules = [] := h
  simp [step, applyEvent, evalRules, hr]

/-- `n` steps with no events. -/
def idleEvents (n : Nat) : List EnvironmentEvent :=
  List.replicate n .idle

/-- **Mass conservation over time.** -/
theorem idleRun_conserves_mass (n : Nat) (w : World) (hrules : w.rules = [])
    (hr : w.laws.massRate = 1) (hm : w.laws.collisions.NoCreation) (hpos : PositiveMass w) :
    totalMass (run w (idleEvents n)).bodies = totalMass w.bodies := by
  induction n generalizing w with
  | zero => rfl
  | succ k ih =>
    have hstep := step_idle_of_no_rules hrules
    have hposNext : PositiveMass (tick w) := tick_positiveMass (by rw [hr]; norm_num) hpos
    have hrun : run w (idleEvents (k + 1)) = run (tick w) (idleEvents k) := by
      show (EnvironmentEvent.idle :: idleEvents k).foldl step w = _
      simp only [List.foldl_cons, hstep]
      rfl
    rw [hrun, ih (tick w) hrules hr hm hposNext, tick_conserves_mass hr hm hpos]

/-- **Energy never rises over time, with no forces and no events.** -/
theorem idleRun_energy_le (n : Nat) (w : World) (hrules : w.rules = []) (hf : w.laws.NoForces)
    (hc : w.laws.collisions = .none ∨ w.laws.collisions = .bounce)
    (he : SafeEnvironment w) (hpos : PositiveMass w) (hr1 : w.laws.massRate ≤ 1) :
    totalEnergy (run w (idleEvents n)).bodies ≤ totalEnergy w.bodies := by
  induction n generalizing w with
  | zero => exact le_rfl
  | succ k ih =>
    have hstep := step_idle_of_no_rules hrules
    have hrun : run w (idleEvents (k + 1)) = run (tick w) (idleEvents k) := by
      show (EnvironmentEvent.idle :: idleEvents k).foldl step w = _
      simp only [List.foldl_cons, hstep]
      rfl
    rw [hrun]
    exact (ih (tick w) hrules hf hc (tick_safe he)
      (tick_positiveMass he.2.2.2.2.2.1 hpos) hr1).trans (tick_energy_le hf hc he hpos hr1)

/-! ## The audit -/

/-- The verdict when a theorem's conditions were checked on this universe. -/
def provenVerdict (claim : Claim) (thm : String) (assumptions : List String) (scope : EventScope)
    (text : String) : Verdict :=
  { claim, status := .proven, theoremId := some thm, assumptions, scope := some scope,
    explanation := text, counterexample := none }

/-- The verdict from searching for a violation. -/
def searchedVerdict (limits : SearchLimits) (claim : Claim) (scope : EventScope) (name : String) :
    World → Verdict := fun w =>
  match searchCounterexample limits scope claim w with
  | some t =>
    { claim, status := .counterexample, theoremId := some (``checkTrace_sound).toString,
      assumptions := [], scope := some scope,
      explanation := s!"{name} fails in this run of {t.events.length} steps.",
      counterexample := some t }
  | none =>
    { claim, status := .unknown, theoremId := none, assumptions := [], scope := none,
      explanation := s!"{name} was neither proved nor broken by the search.",
      counterexample := none }

/-- Is total mass conserved as time passes in this universe? -/
def auditMass (limits : SearchLimits) (w : World) : Verdict :=
  if w.rules = [] ∧ w.laws.massRate = 1 ∧ w.laws.collisions ≠ .spawn ∧ PositiveMass w then
    provenVerdict .massConserved (``idleRun_conserves_mass).toString
      ["The universe has no rules.", "The mass rate is 1.",
       "Collisions do not create bodies.", "Every mass is positive.", "No events happen."]
      .timeOnly "Total mass stays exactly the same as time passes."
  else searchedVerdict limits .massConserved .timeOnly "Mass conservation" w

/-- Does total energy stay level or fall as time passes in this universe? -/
def auditEnergy (limits : SearchLimits) (w : World) : Verdict :=
  if w.rules = [] ∧ w.laws.NoForces ∧ (w.laws.collisions = .none ∨ w.laws.collisions = .bounce) ∧
      SafeEnvironment w ∧ PositiveMass w ∧ w.laws.massRate ≤ 1 then
    provenVerdict .energyNotRising (``idleRun_energy_le).toString
      ["The universe has no rules or forces.", "Bodies bounce or pass through each other.",
       "The environment is safe and the mass rate is at most 1.", "No events happen."]
      .timeOnly "Total kinetic energy can only stay level or fall as time passes."
  else searchedVerdict limits .energyNotRising .timeOnly "Energy not rising" w

/-- Is momentum conserved by bodies acting on each other, along the x axis and along any axis? -/
def auditInteractionMomentum (w : World) : Status × String × List String :=
  let direction : Vec3 := ⟨1, 1, 1⟩
  if w.laws.reaction = 1 ∧ w.laws.collisions.KeepsMomentum ∧ PositiveMass w then
    (.proven, (``interaction_conserves_momentum).toString,
      ["The reaction factor is 1 (Newton's third law).", "Every mass is positive.",
       "Collisions keep momentum. This covers forces between bodies only, not walls or gravity."])
  else
    let bodies := w.bodies.map (accelerate w.laws w.regions)
    let after := (collisionStage w.laws w.nextId (pairAll (forcePair w.laws) bodies)).1
    if totalMomentum direction after ≠ totalMomentum direction bodies then
      (.counterexample, "direct evaluation of the force and collision stages",
        ["Measured on the current bodies, along direction (1, 1, 1)."])
    else
      (.unknown, "", ["The conditions of the theorem do not hold, and these bodies show no change."])

end Paradox

import Paradox.Rules.Semantics
import Paradox.Rules.Analysis
import Paradox.Verification.Facts

/-!
# The rule checker is correct

`Rule.keeps` is a program that reads a rule and answers true or false. The theorems here prove that
"true" can be trusted, for every rule anyone can write.
-/

namespace Paradox

/-! ## Formulas -/

theorem approxSqrt_nonneg (q : ℚ) : 0 ≤ approxSqrt q := by
  unfold approxSqrt
  split
  · exact le_rfl
  · positivity

/-- What `LawExpr.sign` says about a formula is true whenever mass is positive. -/
theorem LawExpr.sign_sound (i : LawInputs) (hm : 0 < i.massA) (hd : 0 ≤ i.distSquared)
    (hs : 0 ≤ i.speedSquared) (e : LawExpr) :
    (e.sign.1 = true → 0 < e.eval i) ∧ (e.sign.2 = true → 0 ≤ e.eval i) := by
  induction e with
  | const q => simp [sign, eval]
  | massA => exact ⟨fun _ => hm, fun _ => hm.le⟩
  | massB => simp [sign]
  | chargeA => simp [sign]
  | chargeB => simp [sign]
  | distSquared => exact ⟨by simp [sign], fun _ => hd⟩
  | dist => exact ⟨by simp [sign], fun _ => approxSqrt_nonneg _⟩
  | speedSquared => exact ⟨by simp [sign], fun _ => hs⟩
  | add a b iha ihb =>
    simp only [sign, Bool.or_eq_true, Bool.and_eq_true, eval]
    refine ⟨?_, fun h => add_nonneg (iha.2 h.1) (ihb.2 h.2)⟩
    rintro (h | h)
    · exact add_pos_of_pos_of_nonneg (iha.1 h.1) (ihb.2 h.2)
    · exact add_pos_of_nonneg_of_pos (iha.2 h.1) (ihb.1 h.2)
  | sub a b iha ihb => simp [sign]
  | mul a b iha ihb =>
    simp only [sign, Bool.and_eq_true, eval]
    exact ⟨fun h => mul_pos (iha.1 h.1) (ihb.1 h.2), fun h => mul_nonneg (iha.2 h.1) (ihb.2 h.2)⟩
  | div a b iha ihb =>
    simp only [sign, Bool.and_eq_true, eval]
    exact ⟨fun h => div_pos (iha.1 h.1) (ihb.1 h.2), fun h => div_nonneg (iha.2 h.1) (ihb.2 h.2)⟩
  | neg a iha => simp [sign]
  | pow a n iha =>
    simp only [sign, Bool.or_eq_true, beq_iff_eq, eval]
    constructor
    · rintro (h | rfl)
      · exact pow_pos (iha.1 h) _
      · simp
    · rintro (h | rfl)
      · exact pow_nonneg (iha.2 h) _
      · simp

/-! ## What rule actions leave alone -/

theorem BodyAction.apply_shape (w : World) (a : BodyAction) (b : Body) :
    (a.apply w b).shape = b.shape := by
  cases a <;> rfl

theorem BodyAction.apply_id (w : World) (a : BodyAction) (b : Body) :
    (a.apply w b).id = b.id := by
  cases a <;> rfl

@[simp] theorem Rule.eval_rules (prev : World) (r : Rule) (w : World) :
    (r.eval prev w).rules = w.rules := by
  induction r generalizing w with
  | create t =>
    simp only [Rule.eval]
    split <;> rfl
  | seq a b iha ihb => simp [Rule.eval, iha, ihb]
  | when c r ih =>
    simp only [Rule.eval]
    split
    · exact ih w
    · rfl
  | _ => rfl

/-- A fact true of every body and kept by the action is true after a body rule. -/
theorem body_forall {Q : Body → Prop} {prev w : World} {c : BodyCond} {a : BodyAction}
    (hQ : ∀ b ∈ w.bodies, Q b) (hA : ∀ b ∈ w.bodies, Q b → Q (a.apply w b)) :
    ∀ x ∈ (Rule.eval prev (.body c a) w).bodies, Q x := by
  intro x hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  split
  · exact hA b hb (hQ b hb)
  · exact hQ b hb

/-! ## The environment stays safe -/

/-- Every rule that passes `envSafe` keeps the environment safe. -/
theorem Rule.envSafe_sound (prev : World) (r : Rule) (w : World) (hr : r.envSafe = true)
    (h : SafeEnvironment w) : SafeEnvironment (r.eval prev w) := by
  induction r generalizing w with
  | skip => exact h
  | body c a =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
    refine body_forall h9 fun b _ hb => ?_
    unfold FitsIn Body.extent at *
    rw [BodyAction.apply_shape]
    exact hb
  | world a =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    cases a with
    | setMaxSpeed v => exact ⟨h1, of_decide_eq_true hr, h3, h4, h5, h6, h7, h8, h9⟩
    | setMassRate v => exact ⟨h1, h2, h3, h4, h5, of_decide_eq_true hr, h7, h8, h9⟩
    | _ => exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  | destroy c =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun b hb => h9 b (List.mem_of_mem_filter hb)⟩
  | create t =>
    simp only [Rule.eval]
    split
    next hc =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
      refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun b hb => ?_⟩
      rcases List.mem_append.mp hb with hb | hb
      · exact h9 b hb
      · rw [List.mem_singleton] at hb
        subst hb
        exact hc.1
    next => exact h
  | seq a b iha ihb =>
    simp only [Rule.envSafe, Bool.and_eq_true] at hr
    exact ihb _ hr.2 (iha _ hr.1 h)
  | when c r ih =>
    simp only [Rule.eval]
    split
    · exact ih _ hr h
    · exact h

/-! ## Body actions -/

theorem BodyAction.keeps_sound (prev : World) (p : Property) (c : BodyCond) (a : BodyAction)
    (w : World) (hk : a.keeps p = true) (he : SafeEnvironment w) (hp : p.holds w) :
    p.holds (Rule.eval prev (.body c a) w) := by
  cases p with
  | positiveMass =>
    refine body_forall (Q := fun b => 0 < b.mass) hp fun b _ hb => ?_
    cases a with
    | scaleMass k => exact mul_pos (of_decide_eq_true hk) hb
    | setMassFormula f =>
      refine (LawExpr.sign_sound _ hb ?_ ?_ f).1 hk
      · show 0 ≤ b.position.x * b.position.x + b.position.y * b.position.y +
          b.position.z * b.position.z
        nlinarith [mul_self_nonneg b.position.x, mul_self_nonneg b.position.y,
          mul_self_nonneg b.position.z]
      · show 0 ≤ b.velocity.x * b.velocity.x + b.velocity.y * b.velocity.y +
          b.velocity.z * b.velocity.z
        nlinarith [mul_self_nonneg b.velocity.x, mul_self_nonneg b.velocity.y,
          mul_self_nonneg b.velocity.z]
    | _ => exact hb
  | boundedPosition =>
    refine body_forall
      (Q := fun b => (w.bounds.inset b.extent).Contains b.position) hp fun b hmem hb => ?_
    cases a with
    | translate d => simp [BodyAction.keeps] at hk
    | clampPosition => exact Bounds.contains_clampPoint (he.2.2.2.2.2.2.2.2 b hmem).2 _
    | _ => exact hb
  | boundedVelocity =>
    refine body_forall (Q := fun b => b.velocity.WithinAbs w.laws.maxSpeed) hp fun b _ hb => ?_
    cases a with
    | applyForce f => simp [BodyAction.keeps] at hk
    | reverseVelocity =>
      exact ⟨(abs_neg _).le.trans hb.1, (abs_neg _).le.trans hb.2.1, (abs_neg _).le.trans hb.2.2⟩
    | rotateVelocity => exact ⟨hb.2.2, hb.2.1, (abs_neg _).le.trans hb.1⟩
    | scaleVelocity k =>
      have hk' : |k| ≤ 1 := of_decide_eq_true hk
      have key : ∀ x : ℚ, |k * x| ≤ |x| := fun x => by
        rw [abs_mul]; nlinarith [abs_nonneg x]
      exact withinAbs_of_le hb (key _) (key _) (key _)
    | clampVelocity => exact Vec3.withinAbs_clampAbs _ he.2.1.le
    | _ => exact hb
  | safeEnvironment => exact Rule.envSafe_sound prev (.body c a) w rfl he
  | uniqueIds =>
    have hids : (Rule.eval prev (.body c a) w).bodies.map Body.id = w.bodies.map Body.id := by
      show (w.bodies.map fun b => if c.test prev b then a.apply w b else b).map Body.id = _
      rw [List.map_map]
      refine List.map_congr_left fun b _ => ?_
      dsimp only [Function.comp]
      split
      · exact BodyAction.apply_id w a b
      · rfl
    refine ⟨hids ▸ hp.1, ?_⟩
    refine body_forall (Q := fun b => b.id < w.nextId) hp.2 fun b _ hb => ?_
    rw [BodyAction.apply_id]
    exact hb

/-! ## Rules that make a property true -/

/-- A rule that passes `establishes` makes the property true, whatever it was before. -/
theorem Rule.establishes_sound (prev : World) (p : Property) (r : Rule) (w : World)
    (hk : r.establishes p = true) (he : SafeEnvironment w) : p.holds (r.eval prev w) := by
  induction r generalizing w with
  | body c a =>
    cases c <;> cases a <;> simp only [Rule.establishes] at hk <;> try contradiction
    · have hp : p = .boundedVelocity := by simpa using hk
      subst hp
      intro x hx
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
      exact Vec3.withinAbs_clampAbs _ he.2.1.le
    · have hp : p = .boundedPosition := by simpa using hk
      subst hp
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact Bounds.contains_clampPoint (he.2.2.2.2.2.2.2.2 b hb).2 _
  | seq a b _ ihb =>
    simp only [Rule.establishes, Bool.and_eq_true] at hk
    exact ihb _ hk.2 (Rule.envSafe_sound prev a w hk.1 he)
  | _ => simp [Rule.establishes] at hk

/-! ## The main soundness theorem -/

theorem WorldAction.keeps_sound (prev : World) (p : Property) (a : WorldAction) (w : World)
    (hk : a.keeps p = true) (he : SafeEnvironment w) (hp : p.holds w) :
    p.holds (Rule.eval prev (.world a) w) := by
  cases p with
  | safeEnvironment =>
    refine Rule.envSafe_sound prev (.world a) w ?_ he
    cases a <;> first | rfl | exact hk
  | boundedVelocity =>
    cases a with
    | setMaxSpeed v => simp [WorldAction.keeps] at hk
    | _ => exact hp
  | positiveMass | boundedPosition | uniqueIds => exact hp

/-- **If the rule checker says a rule keeps a property, the rule keeps that property**, for every
rule, in every safe world. -/
theorem Rule.keeps_sound (prev : World) (p : Property) (r : Rule) (w : World)
    (hk : r.keeps p = true) (he : SafeEnvironment w) (hp : p.holds w) :
    p.holds (r.eval prev w) := by
  induction r generalizing w with
  | skip => exact hp
  | body c a => exact BodyAction.keeps_sound prev p c a w hk he hp
  | world a => exact WorldAction.keeps_sound prev p a w hk he hp
  | destroy c =>
    cases p with
    | positiveMass => exact fun b hb => hp b (List.mem_of_mem_filter hb)
    | boundedPosition => exact fun b hb => hp b (List.mem_of_mem_filter hb)
    | boundedVelocity => exact fun b hb => hp b (List.mem_of_mem_filter hb)
    | safeEnvironment => exact Rule.envSafe_sound prev (.destroy c) w rfl he
    | uniqueIds =>
      refine ⟨?_, fun b hb => hp.2 b (List.mem_of_mem_filter hb)⟩
      exact (List.Sublist.map _ List.filter_sublist).nodup hp.1
  | create t =>
    cases p with
    | safeEnvironment => exact Rule.envSafe_sound prev (.create t) w rfl he
    | _ =>
      simp only [Rule.eval]
      split
      next hc =>
        obtain ⟨hfit, hmass, hin, hvel, -⟩ := hc
        first
        | (intro b hb
           rcases List.mem_append.mp hb with hb | hb
           · exact hp b hb
           · rw [List.mem_singleton] at hb
             subst hb
             first | exact hmass | exact hin | exact hvel)
        | (refine ⟨?_, fun b hb => ?_⟩
           · simp only [List.map_append, List.map_cons, List.map_nil]
             refine List.nodup_append.mpr ⟨hp.1, by simp, ?_⟩
             intro x hx y hy
             obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
             simp only [List.mem_singleton] at hy
             subst hy
             exact Nat.ne_of_lt (hp.2 c hc)
           · rcases List.mem_append.mp hb with hb | hb
             · exact Nat.lt_succ_of_lt (hp.2 b hb)
             · rw [List.mem_singleton] at hb
               subst hb
               exact Nat.lt_succ_self _)
      next => exact hp
  | seq a b iha ihb =>
    simp only [Rule.keeps, Bool.and_eq_true, Bool.or_eq_true] at hk
    obtain ⟨hsafe, hk | hk⟩ := hk
    · exact ihb _ hk.2 (Rule.envSafe_sound prev a w hsafe he) (iha _ hk.1 he hp)
    · exact Rule.establishes_sound prev p b _ hk (Rule.envSafe_sound prev a w hsafe he)
  | when c r ih =>
    simp only [Rule.eval]
    split
    · exact ih _ hk he hp
    · exact hp

/-- A certified rule passes both checks for every property. -/
theorem Rule.certified_parts {r : Rule} (h : r.certified = true) (p : Property) :
    r.envSafe = true ∧ r.keeps p = true := by
  simp only [Rule.certified, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1, by simpa using h.2 p (Property.mem_all p)⟩

/-- A repaired rule passes the check. -/
theorem Rule.repair_certified {r r' : Rule} (h : r.repair = some r') : r'.certified = true := by
  simp only [Rule.repair] at h
  split at h
  next hc =>
    simp only [Option.some.injEq] at h
    exact h ▸ hc
  next => simp at h

/-! ## The running rule list -/

/-- A list of checked rules keeps the property and the environment. -/
theorem evalRules_sound (prev : World) (p : Property) (rs : List Rule) (w : World)
    (hrs : ∀ r ∈ rs, r.envSafe = true ∧ r.keeps p = true)
    (he : SafeEnvironment w) (hp : p.holds w) :
    SafeEnvironment (evalRules prev rs w) ∧ p.holds (evalRules prev rs w) := by
  induction rs generalizing w with
  | nil => exact ⟨he, hp⟩
  | cons r rest ih =>
    have hr := hrs r List.mem_cons_self
    exact ih _ (fun x hx => hrs x (List.mem_cons_of_mem _ hx))
      (Rule.envSafe_sound prev r w hr.1 he) (Rule.keeps_sound prev p r w hr.2 he hp)

@[simp] theorem evalRules_rules (prev : World) (rs : List Rule) (w : World) :
    (evalRules prev rs w).rules = w.rules := by
  induction rs generalizing w with
  | nil => rfl
  | cons r rest ih =>
    show (evalRules prev rest (r.eval prev w)).rules = w.rules
    rw [ih, Rule.eval_rules]

end Paradox

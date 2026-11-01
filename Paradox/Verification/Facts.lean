import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Paradox.Spec

/-!
# Supporting lemmas

The theorems people read are in `Paradox/Proofs.lean`. This file holds the steps they rest on.
-/

namespace Paradox

/-! ## The pair traversal -/

theorem pairOne_forall {f : Body → Body → Body × Body} {Q : Body → Prop}
    (hf : ∀ a b, Q a → Q b → Q (f a b).1 ∧ Q (f a b).2) (l : List Body) (a : Body)
    (ha : Q a) (hl : ∀ x ∈ l, Q x) :
    Q (pairOne f a l).1 ∧ ∀ x ∈ (pairOne f a l).2, Q x := by
  induction l generalizing a with
  | nil => simpa [pairOne] using ha
  | cons c cs ih =>
    have p := hf a c ha (hl c List.mem_cons_self)
    have r := ih (f a c).1 p.1 (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    refine ⟨r.1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | h
    · exact p.2
    · exact r.2 x h

theorem pairAll_forall {f : Body → Body → Body × Body} {Q : Body → Prop}
    (hf : ∀ a b, Q a → Q b → Q (f a b).1 ∧ Q (f a b).2) (l : List Body)
    (hl : ∀ x ∈ l, Q x) : ∀ x ∈ pairAll f l, Q x := by
  induction l with
  | nil => simp [pairAll]
  | cons b bs ih =>
    have ih' := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    have r := pairOne_forall hf (pairAll f bs) b (hl b List.mem_cons_self) ih'
    intro x hx
    rcases List.mem_cons.mp hx with rfl | h
    · exact r.1
    · exact r.2 x h

/-- The total of a per-body quantity. -/
def total (Q : Body → ℚ) (l : List Body) : ℚ :=
  (l.map Q).sum

theorem pairOne_total {f : Body → Body → Body × Body} {Q : Body → ℚ} {G : Body → Prop}
    (hG : ∀ a b, G a → G b → G (f a b).1 ∧ G (f a b).2)
    (hf : ∀ a b, G a → G b → Q (f a b).1 + Q (f a b).2 = Q a + Q b)
    (l : List Body) (a : Body) (ha : G a) (hl : ∀ x ∈ l, G x) :
    Q (pairOne f a l).1 + total Q (pairOne f a l).2 = Q a + total Q l := by
  induction l generalizing a with
  | nil => simp [pairOne, total]
  | cons c cs ih =>
    have hc := hl c List.mem_cons_self
    have h1 := hf a c ha hc
    have h2 := ih (f a c).1 (hG a c ha hc).1 (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    simp only [pairOne, total, List.map_cons, List.sum_cons] at h2 ⊢
    linarith

theorem pairAll_total {f : Body → Body → Body × Body} {Q : Body → ℚ} {G : Body → Prop}
    (hG : ∀ a b, G a → G b → G (f a b).1 ∧ G (f a b).2)
    (hf : ∀ a b, G a → G b → Q (f a b).1 + Q (f a b).2 = Q a + Q b)
    (l : List Body) (hl : ∀ x ∈ l, G x) : total Q (pairAll f l) = total Q l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    have hb := hl b List.mem_cons_self
    have hbs : ∀ x ∈ bs, G x := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have h1 := pairOne_total hG hf (pairAll f bs) b hb (pairAll_forall hG bs hbs)
    have h2 := ih hbs
    simp only [pairAll, total, List.map_cons, List.sum_cons] at h1 h2 ⊢
    linarith

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

/-! ## What survives a step -/

/-- A fact about a body that does not depend on its velocity survives the forces. -/
theorem forcesStage_forall {Q : Body → Prop} (hv : ∀ (b : Body) v, Q b → Q { b with velocity := v })
    (l : Laws) (bs : List Body) (hl : ∀ x ∈ bs, Q x) : ∀ x ∈ forcesStage l bs, Q x := by
  refine pairAll_forall (fun a b ha hb => ⟨hv a _ ha, ?_⟩) _ ?_
  · unfold pullPair
    dsimp only
    split
    · exact hv b _ hb
    · exact hb
  · intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact hv b _ (hl b hb)

/-- Every body after a step comes from a body after the forces. -/
theorem mem_tick {w : World} {b' : Body} (h : b' ∈ (tick w).bodies) :
    ∃ b ∈ forcesStage w.laws w.bodies,
      b' = finishBody w.laws (moveBody w (limitSpeed w.laws b)) := by
  have h' : b' ∈ (((forcesStage w.laws w.bodies).map (limitSpeed w.laws)).map (moveBody w)).map
      (finishBody w.laws) := h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h'
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hd
  exact ⟨b, hb, rfl⟩

/-- The world stays well-formed. -/
theorem tick_wellFormed {w : World} (h : WellFormed w) : WellFormed (tick w) := by
  refine ⟨h.1, fun b' hb' => ?_⟩
  obtain ⟨b, hb, rfl⟩ := mem_tick hb'
  exact forcesStage_forall (Q := BodyOk w.bounds) (fun _ _ hx => hx) _ _ h.2 b hb

theorem tick_laws (w : World) : (tick w).laws = w.laws := rfl

theorem run_laws (n : Nat) (w : World) : (run n w).laws = w.laws := by
  induction n generalizing w with
  | zero => rfl
  | succ k ih => exact (ih (tick w)).trans (tick_laws w)

theorem run_wellFormed (n : Nat) {w : World} (h : WellFormed w) : WellFormed (run n w) := by
  induction n generalizing w with
  | zero => exact h
  | succ k ih => exact ih (tick_wellFormed h)

/-! ## Speed -/

/-- Moving never makes an object faster along an axis, if a bounce cannot add speed. -/
theorem abs_moveAxis_snd_le {e : ℚ} (dt lo hi p v : ℚ) (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    |(moveAxis e dt lo hi p v).2| ≤ |v| := by
  have hb : |(-(e * v))| ≤ |v| := by
    rw [abs_neg, abs_mul, abs_of_nonneg h0]
    nlinarith [abs_nonneg v]
  unfold moveAxis
  dsimp only
  split
  · exact hb
  · split
    · exact hb
    · exact le_rfl

theorem withinAbs_of_le {a b : Vec3} {m : ℚ} (h : b.WithinAbs m)
    (hx : |a.x| ≤ |b.x|) (hy : |a.y| ≤ |b.y|) (hz : |a.z| ≤ |b.z|) : a.WithinAbs m :=
  ⟨hx.trans h.1, hy.trans h.2.1, hz.trans h.2.2⟩

/-- Moving keeps a velocity within any limit it was already within, if a bounce cannot add speed. -/
theorem moveBody_withinAbs {w : World} {b : Body} {m : ℚ}
    (h0 : 0 ≤ w.laws.restitution) (h1 : w.laws.restitution ≤ 1) (hv : b.velocity.WithinAbs m) :
    (moveBody w b).velocity.WithinAbs m := by
  unfold moveBody
  dsimp only
  refine withinAbs_of_le (withinAbs_of_le hv ?_ ?_ ?_)
    (abs_snap_le _ _) (abs_snap_le _ _) (abs_snap_le _ _)
  all_goals exact abs_moveAxis_snd_le _ _ _ _ _ h0 h1

theorem abs_mul_le_of_abs_le_one {k : ℚ} (hk : |k| ≤ 1) (x : ℚ) : |k * x| ≤ |x| := by
  rw [abs_mul]
  nlinarith [abs_nonneg x]

/-- Multiplying by something of size at most 1 keeps a velocity within any limit. -/
theorem scale_withinAbs {k m : ℚ} (hk : |k| ≤ 1) {v : Vec3} (h : v.WithinAbs m) :
    (v.scale k).WithinAbs m :=
  ⟨(abs_mul_le_of_abs_le_one hk _).trans h.1, (abs_mul_le_of_abs_le_one hk _).trans h.2.1,
   (abs_mul_le_of_abs_le_one hk _).trans h.2.2⟩

/-- After the speed limit and a move, a velocity is within the limit, if a bounce cannot add speed. -/
theorem moved_withinAbs {w : World} (b : Body) (hm : 0 ≤ w.laws.maxSpeed)
    (h0 : 0 ≤ w.laws.restitution) (h1 : w.laws.restitution ≤ 1) :
    (moveBody w (limitSpeed w.laws b)).velocity.WithinAbs w.laws.maxSpeed :=
  moveBody_withinAbs h0 h1 (Vec3.withinAbs_clampAbs _ hm)

/-! ## Momentum -/

/-- With Newton's third law on or no pull, a pair keeps its momentum, whatever the pull is. -/
theorem pullPair_momentum (l : Laws) (hl : MomentumSafe l) (c : Vec3) (a b : Body)
    (ha : 0 < a.mass) (hb : 0 < b.mass) :
    (pullPair l a b).1.mass * (pullPair l a b).1.velocity.dot c +
        (pullPair l a b).2.mass * (pullPair l a b).2.velocity.dot c =
      a.mass * a.velocity.dot c + b.mass * b.velocity.dot c := by
  have ha' := ha.ne'
  have hb' := hb.ne'
  rcases hl with h | h
  · simp only [pullPair, h, if_true, Vec3.dot, Vec3.add, Vec3.sub, Vec3.scale]
    field_simp
    ring
  · simp only [pullPair, pullAmount, h]
    split <;> simp [Vec3.dot, Vec3.add, Vec3.sub, Vec3.scale]

/-- The pull stage keeps every object's mass. -/
theorem pullPair_positive (l : Laws) (a b : Body) (ha : 0 < a.mass) (hb : 0 < b.mass) :
    0 < (pullPair l a b).1.mass ∧ 0 < (pullPair l a b).2.mass := by
  refine ⟨ha, ?_⟩
  unfold pullPair
  dsimp only
  split
  · exact hb
  · exact hb

/-! ## Energy -/

/-- The kinetic energy of one object. -/
def energyOf (b : Body) : ℚ :=
  b.mass * b.velocity.dot b.velocity / 2

theorem totalEnergy_eq (bs : List Body) : totalEnergy bs = total energyOf bs := rfl

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

theorem clamp_of_mem {x lo hi : ℚ} (h1 : lo ≤ x) (h2 : x ≤ hi) : clamp x lo hi = x := by
  unfold clamp
  rw [min_eq_left h2, max_eq_right h1]

theorem abs_clampAbs_le_abs (x : ℚ) {m : ℚ} (hm : 0 ≤ m) : |clampAbs x m| ≤ |x| := by
  by_cases h : |x| ≤ m
  · rw [show clampAbs x m = x from clamp_of_mem (abs_le.mp h).1 (abs_le.mp h).2]
  · exact (abs_clampAbs_le x hm).trans (not_le.mp h).le

/-- With no gravity and no pull, the forces change nothing. -/
theorem forcesStage_of_energySafe {l : Laws} (h : EnergySafe l) (bs : List Body) :
    forcesStage l bs = bs := by
  have hg : applyGravity l = id := by
    funext b
    simp [applyGravity, h.1, Vec3.add]
  have hp : ∀ a b, pullPair l a b = (a, b) := by
    intro a b
    simp only [pullPair, pullAmount, h.2.1]
    split <;> simp [Vec3.add, Vec3.sub, Vec3.scale]
  unfold forcesStage pullStage
  rw [pairAll_identity hp, hg, List.map_id]

/-- One object's energy does not rise over a step, when nothing can add speed. -/
theorem step_energy_le {w : World} (hok : LawsOk w.laws) (hs : EnergySafe w.laws) {b : Body}
    (hb : 0 < b.mass) :
    energyOf (finishBody w.laws (moveBody w (limitSpeed w.laws b))) ≤ energyOf b := by
  have hm := hok.1.le
  have he0 := hok.2.2
  have he1 := hs.2.2.1
  have hk := hs.2.2.2
  set moved := moveBody w (limitSpeed w.laws b) with hmoved
  have hlimit : (limitSpeed w.laws b).velocity.dot (limitSpeed w.laws b).velocity ≤
      b.velocity.dot b.velocity :=
    dot_self_le (abs_clampAbs_le_abs _ hm) (abs_clampAbs_le_abs _ hm) (abs_clampAbs_le_abs _ hm)
  have hmove : moved.velocity.dot moved.velocity ≤
      (limitSpeed w.laws b).velocity.dot (limitSpeed w.laws b).velocity := by
    rw [hmoved]
    unfold moveBody
    dsimp only
    refine le_trans (dot_self_le (abs_snap_le _ _) (abs_snap_le _ _) (abs_snap_le _ _)) ?_
    exact dot_self_le (abs_moveAxis_snd_le _ _ _ _ _ he0 he1)
      (abs_moveAxis_snd_le _ _ _ _ _ he0 he1) (abs_moveAxis_snd_le _ _ _ _ _ he0 he1)
  have hscale : (moved.velocity.scale w.laws.multiplier).dot
      (moved.velocity.scale w.laws.multiplier) ≤ moved.velocity.dot moved.velocity :=
    dot_self_le (abs_mul_le_of_abs_le_one hk _) (abs_mul_le_of_abs_le_one hk _)
      (abs_mul_le_of_abs_le_one hk _)
  have hfinish : (finishBody w.laws moved).velocity.dot (finishBody w.laws moved).velocity ≤
      moved.velocity.dot moved.velocity := by
    unfold finishBody
    dsimp only
    split
    · refine le_trans (dot_self_le (abs_clampAbs_le_abs _ hm) (abs_clampAbs_le_abs _ hm)
        (abs_clampAbs_le_abs _ hm)) hscale
    · exact hscale
  have hall := hfinish.trans (hmove.trans hlimit)
  have : b.mass * (finishBody w.laws moved).velocity.dot (finishBody w.laws moved).velocity ≤
      b.mass * b.velocity.dot b.velocity := mul_le_mul_of_nonneg_left hall hb.le
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

end Paradox

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Paradox.Verification.Facts

/-!
# Conservation laws

Which quantities stay the same depends on the laws the user picks. These theorems say exactly when
each one holds. Violations under other laws are real and can be shown with concrete runs.
-/

namespace Paradox

/-- The total of some per-body quantity. -/
def total (Q : Body → ℚ) (l : List Body) : ℚ :=
  (l.map Q).sum

/-- Momentum of one body along direction `c`. -/
def momentumAlong (c : Vec3) (b : Body) : ℚ :=
  b.mass * b.velocity.dot c

/-- Kinetic energy of one body. -/
def kineticEnergy (b : Body) : ℚ :=
  b.mass * b.velocity.dot b.velocity / 2

/-- The total momentum of a list of bodies along direction `c`. -/
def totalMomentum (c : Vec3) (l : List Body) : ℚ := total (momentumAlong c) l

/-- The total kinetic energy of a list of bodies. -/
def totalEnergy (l : List Body) : ℚ := total kineticEnergy l

/-- The total mass of a list of bodies. -/
def totalMass (l : List Body) : ℚ := total Body.mass l

/-! ## Pair interactions: if each pair keeps a total, the whole list does -/

section Pairs

variable {f : Body → Body → Body × Body} {Q : Body → ℚ} {G : Body → Prop}

theorem pairOne_total_le
    (hG : ∀ a b, G a → G b → G (f a b).1 ∧ G (f a b).2)
    (hf : ∀ a b, G a → G b → Q (f a b).1 + Q (f a b).2 ≤ Q a + Q b)
    (l : List Body) (a : Body) (ha : G a) (hl : ∀ x ∈ l, G x) :
    Q (pairOne f a l).1 + total Q (pairOne f a l).2 ≤ Q a + total Q l := by
  induction l generalizing a with
  | nil => simp [pairOne, total]
  | cons c cs ih =>
    have hc := hl c List.mem_cons_self
    have h1 := hf a c ha hc
    have h2 := ih (f a c).1 (hG a c ha hc).1 (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    simp only [pairOne, total, List.map_cons, List.sum_cons] at h2 ⊢
    linarith

theorem pairOne_total_eq
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

theorem pairAll_total_eq
    (hG : ∀ a b, G a → G b → G (f a b).1 ∧ G (f a b).2)
    (hf : ∀ a b, G a → G b → Q (f a b).1 + Q (f a b).2 = Q a + Q b)
    (l : List Body) (hl : ∀ x ∈ l, G x) : total Q (pairAll f l) = total Q l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    have hb := hl b List.mem_cons_self
    have hbs : ∀ x ∈ bs, G x := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have h1 := pairOne_total_eq hG hf (pairAll f bs) b hb (pairAll_forall hG bs hbs)
    have h2 := ih hbs
    simp only [pairAll, total, List.map_cons, List.sum_cons] at h1 h2 ⊢
    linarith

theorem pairAll_total_le
    (hG : ∀ a b, G a → G b → G (f a b).1 ∧ G (f a b).2)
    (hf : ∀ a b, G a → G b → Q (f a b).1 + Q (f a b).2 ≤ Q a + Q b)
    (l : List Body) (hl : ∀ x ∈ l, G x) : total Q (pairAll f l) ≤ total Q l := by
  induction l with
  | nil => exact le_rfl
  | cons b bs ih =>
    have hb := hl b List.mem_cons_self
    have hbs : ∀ x ∈ bs, G x := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have h1 := pairOne_total_le hG hf (pairAll f bs) b hb (pairAll_forall hG bs hbs)
    have h2 := ih hbs
    simp only [pairAll, total, List.map_cons, List.sum_cons] at h1 h2 ⊢
    linarith

end Pairs

/-! ## Invented forces and momentum -/

/-- **Newton's third law gives momentum conservation, for every force formula.** If the reaction
factor is 1 and masses are positive, the invented force does not change momentum between two bodies,
whatever the formula says. -/
theorem forcePair_momentum (laws : PhysicsLaws) (hr : laws.reaction = 1) (c : Vec3) (a b : Body)
    (ha : 0 < a.mass) (hb : 0 < b.mass) :
    momentumAlong c (forcePair laws a b).1 + momentumAlong c (forcePair laws a b).2 =
      momentumAlong c a + momentumAlong c b := by
  have ha' := ha.ne'
  have hb' := hb.ne'
  simp only [forcePair, momentumAlong, hr, Vec3.dot, Vec3.add, Vec3.sub, Vec3.scale]
  field_simp
  ring

/-- **Momentum survives every invented force law.** With Newton's third law on, one pass of the
pair force over all bodies keeps total momentum along any direction, for every formula. -/
theorem pairForces_conserve_momentum (laws : PhysicsLaws) (hr : laws.reaction = 1) (c : Vec3)
    (l : List Body) (hl : ∀ x ∈ l, 0 < x.mass) :
    totalMomentum c (pairAll (forcePair laws) l) = totalMomentum c l :=
  pairAll_total_eq (G := fun x => 0 < x.mass) (fun _ _ ha hb => ⟨ha, hb⟩)
    (fun a b ha hb => forcePair_momentum laws hr c a b ha hb) l hl

/-! ## Collisions -/

/-- A bounce keeps momentum between two bodies. -/
theorem bouncePair_momentum (e : ℚ) (c : Vec3) (a b : Body) (ha : 0 < a.mass) (hb : 0 < b.mass) :
    momentumAlong c (bouncePair e a b).1 + momentumAlong c (bouncePair e a b).2 =
      momentumAlong c a + momentumAlong c b := by
  unfold bouncePair
  dsimp only
  split
  · simp only [momentumAlong, Vec3.dot, Vec3.add, Vec3.sub, Vec3.scale]
    ring
  · rfl

/-- Bouncing keeps total momentum along any direction, for any restitution. -/
theorem bounces_conserve_momentum (e : ℚ) (c : Vec3) (l : List Body) (hl : ∀ x ∈ l, 0 < x.mass) :
    totalMomentum c (pairAll (bouncePair e) l) = totalMomentum c l := by
  refine pairAll_total_eq (G := fun x => 0 < x.mass) (fun a b ha hb => ?_)
    (fun a b ha hb => bouncePair_momentum e c a b ha hb) l hl
  unfold bouncePair
  dsimp only
  split
  · exact ⟨ha, hb⟩
  · exact ⟨ha, hb⟩

/-- A bounce with `0 ≤ e ≤ 1` never adds energy between two bodies. -/
theorem bouncePair_energy {e : ℚ} (h0 : 0 ≤ e) (h1 : e ≤ 1) (a b : Body)
    (ha : 0 < a.mass) (hb : 0 < b.mass) :
    kineticEnergy (bouncePair e a b).1 + kineticEnergy (bouncePair e a b).2 ≤
      kineticEnergy a + kineticEnergy b := by
  unfold bouncePair
  dsimp only
  split
  next hc =>
    obtain ⟨-, hnn, happ⟩ := hc
    set n := b.position.sub a.position with hn
    set nn := n.dot n with hnndef
    set approach := (a.velocity.sub b.velocity).dot n with happdef
    have hM : 0 < a.mass + b.mass := add_pos ha hb
    set k := (1 + e) * (approach / nn) / (a.mass + b.mass) with hk
    have hkpos : 0 ≤ k := by positivity
    have hkey : k * (a.mass + b.mass) * nn = (1 + e) * approach := by
      rw [hk]; field_simp
    have hdiff : kineticEnergy { a with velocity := a.velocity.sub (n.scale (k * b.mass)) } +
        kineticEnergy { b with velocity := b.velocity.add (n.scale (k * a.mass)) } -
        (kineticEnergy a + kineticEnergy b) =
        k * a.mass * b.mass / 2 * (k * (a.mass + b.mass) * nn - 2 * approach) := by
      simp only [kineticEnergy, hnndef, happdef, Vec3.dot, Vec3.add, Vec3.sub, Vec3.scale]
      ring
    rw [hkey] at hdiff
    have hneg : k * a.mass * b.mass / 2 * ((1 + e) * approach - 2 * approach) ≤ 0 := by
      have h3 : (1 + e) * approach - 2 * approach ≤ 0 := by nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h3
    linarith
  next => exact le_rfl

/-- A pass of bounces never adds energy. -/
theorem bounces_energy {e : ℚ} (h0 : 0 ≤ e) (h1 : e ≤ 1) (l : List Body)
    (hl : ∀ x ∈ l, 0 < x.mass) :
    totalEnergy (pairAll (bouncePair e) l) ≤ totalEnergy l := by
  refine pairAll_total_le (G := fun x => 0 < x.mass) (fun a b ha hb => ?_)
    (fun a b ha hb => bouncePair_energy h0 h1 a b ha hb) l hl
  unfold bouncePair
  dsimp only
  split
  · exact ⟨ha, hb⟩
  · exact ⟨ha, hb⟩

/-- At restitution 1, a bounce keeps energy exactly. -/
theorem bouncePair_energy_elastic (a b : Body) (ha : 0 < a.mass) (hb : 0 < b.mass) :
    kineticEnergy (bouncePair 1 a b).1 + kineticEnergy (bouncePair 1 a b).2 =
      kineticEnergy a + kineticEnergy b := by
  unfold bouncePair
  dsimp only
  split
  next hc =>
    obtain ⟨-, hnn, happ⟩ := hc
    set n := b.position.sub a.position with hn
    set nn := n.dot n with hnndef
    set approach := (a.velocity.sub b.velocity).dot n with happdef
    have hM : 0 < a.mass + b.mass := add_pos ha hb
    set k := (1 + 1) * (approach / nn) / (a.mass + b.mass) with hk
    have hkey : k * (a.mass + b.mass) * nn = 2 * approach := by
      rw [hk]; field_simp; ring
    have hdiff : kineticEnergy { a with velocity := a.velocity.sub (n.scale (k * b.mass)) } +
        kineticEnergy { b with velocity := b.velocity.add (n.scale (k * a.mass)) } -
        (kineticEnergy a + kineticEnergy b) =
        k * a.mass * b.mass / 2 * (k * (a.mass + b.mass) * nn - 2 * approach) := by
      simp only [kineticEnergy, hnndef, happdef, Vec3.dot, Vec3.add, Vec3.sub, Vec3.scale]
      ring
    rw [hkey] at hdiff
    have : kineticEnergy { a with velocity := a.velocity.sub (n.scale (k * b.mass)) } +
        kineticEnergy { b with velocity := b.velocity.add (n.scale (k * a.mass)) } -
        (kineticEnergy a + kineticEnergy b) = 0 := by
      rw [hdiff]; ring
    linarith
  next => rfl

/-! ## Merging -/

theorem mergeBodies_mass (a b : Body) : (mergeBodies a b).mass = a.mass + b.mass := rfl

/-- Merging keeps momentum between two bodies. -/
theorem mergeBodies_momentum (c : Vec3) (a b : Body) (ha : 0 < a.mass) (hb : 0 < b.mass) :
    momentumAlong c (mergeBodies a b) = momentumAlong c a + momentumAlong c b := by
  have hM : a.mass + b.mass ≠ 0 := (add_pos ha hb).ne'
  simp only [mergeBodies, momentumAlong, Vec3.dot, Vec3.add, Vec3.scale]
  field_simp
  ring

/-- Any quantity that merging adds up is kept by `mergeOne`. -/
theorem mergeOne_total {Q : Body → ℚ} {G : Body → Prop}
    (hG : ∀ a b, G a → G b → G (mergeBodies a b))
    (hQ : ∀ a b, G a → G b → Q (mergeBodies a b) = Q a + Q b)
    (l : List Body) (a : Body) (ha : G a) (hl : ∀ x ∈ l, G x) :
    total Q (mergeOne a l) = Q a + total Q l := by
  induction l with
  | nil => simp [mergeOne, total]
  | cons c cs ih =>
    have hc := hl c List.mem_cons_self
    simp only [mergeOne]
    split
    · simp only [total, List.map_cons, List.sum_cons]
      rw [hQ a c ha hc]
      ring
    · have := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
      simp only [total, List.map_cons, List.sum_cons] at this ⊢
      rw [this]
      ring

/-- A pass of merges keeps any quantity that merging adds up. -/
theorem mergeAll_total {Q : Body → ℚ} {G : Body → Prop}
    (hc : StageClosed G)
    (hQ : ∀ a b, G a → G b → Q (mergeBodies a b) = Q a + Q b)
    (l : List Body) (hl : ∀ x ∈ l, G x) : total Q (mergeAll l) = total Q l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    have hb := hl b List.mem_cons_self
    have hbs : ∀ x ∈ bs, G x := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have h1 := mergeOne_total hc.merge hQ (mergeAll bs) b hb (mergeAll_forall hc bs hbs)
    have h2 := ih hbs
    show total Q (mergeOne b (mergeAll bs)) = total Q (b :: bs)
    rw [h1, h2]
    simp [total]

/-- Merging keeps total momentum along any direction. -/
theorem merges_conserve_momentum (c : Vec3) (l : List Body) (hl : ∀ x ∈ l, 0 < x.mass) :
    totalMomentum c (mergeAll l) = totalMomentum c l :=
  mergeAll_total positiveMass_stageClosed (fun a b ha hb => mergeBodies_momentum c a b ha hb) l hl

/-- Merging keeps total mass. -/
theorem merges_conserve_mass (l : List Body) (hl : ∀ x ∈ l, 0 < x.mass) :
    totalMass (mergeAll l) = totalMass l :=
  mergeAll_total positiveMass_stageClosed (fun a b _ _ => mergeBodies_mass a b) l hl

/-! ## Total mass over a whole tick -/

/-- A collision mode that does not create bodies. -/
def CollisionMode.NoCreation : CollisionMode → Prop
  | .spawn => False
  | _ => True

/-- The collision stage keeps total mass, unless it creates bodies. -/
theorem collisionStage_mass (laws : PhysicsLaws) (hm : laws.collisions.NoCreation) (nextId : Nat)
    (l : List Body) (hl : ∀ x ∈ l, 0 < x.mass) :
    totalMass (collisionStage laws nextId l).1 = totalMass l := by
  have pairCase : ∀ f : Body → Body → Body × Body,
      (∀ a b, 0 < a.mass → 0 < b.mass → 0 < (f a b).1.mass ∧ 0 < (f a b).2.mass) →
      (∀ a b, (f a b).1.mass + (f a b).2.mass = a.mass + b.mass) →
      total Body.mass (pairAll f l) = total Body.mass l := by
    intro f hG hf
    exact pairAll_total_eq (G := fun x => 0 < x.mass) hG (fun a b _ _ => hf a b) l hl
  unfold collisionStage totalMass
  split
  next => rfl
  next =>
    refine pairCase _ (fun a b ha hb => ?_) (fun a b => ?_) <;>
    · unfold bouncePair
      dsimp only
      split
      · first | exact ⟨ha, hb⟩ | rfl
      · first | exact ⟨ha, hb⟩ | rfl
  next =>
    refine pairCase _ (fun a b ha hb => ?_) (fun a b => ?_) <;>
    · unfold exchangeVelocityPair
      split
      · first | exact ⟨ha, hb⟩ | rfl
      · first | exact ⟨ha, hb⟩ | rfl
  next =>
    refine pairCase _ (fun a b ha hb => ?_) (fun a b => ?_)
    · unfold exchangeMassPair
      split
      · exact ⟨hb, ha⟩
      · exact ⟨ha, hb⟩
    · unfold exchangeMassPair
      split
      · exact add_comm _ _
      · rfl
  next => exact merges_conserve_mass l hl
  next heq =>
    rw [heq] at hm
    exact hm.elim

theorem total_map_eq {Q : Body → ℚ} {f : Body → Body} (hf : ∀ b, Q (f b) = Q b) (l : List Body) :
    total Q (l.map f) = total Q l := by
  simp only [total, List.map_map]
  congr 1
  exact List.map_congr_left fun b _ => hf b

/-- **Mass conservation.** If masses are positive, the mass rate is 1, and collisions do not create
bodies, a tick keeps total mass exactly, whatever the other laws are. -/
theorem tick_conserves_mass {w : World} (hr : w.laws.massRate = 1)
    (hm : w.laws.collisions.NoCreation) (hl : PositiveMass w) :
    totalMass (tick w).bodies = totalMass w.bodies := by
  have hforcedPos : ∀ x ∈ applyForces w, 0 < x.mass := by
    refine pairAll_forall (Q := fun x => 0 < x.mass) (fun _ _ ha hb => ⟨ha, hb⟩) _ ?_
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact hl b hb
  have hforced : totalMass (applyForces w) = totalMass w.bodies := by
    have h1 : total Body.mass (applyForces w) =
        total Body.mass (w.bodies.map (accelerate w.laws w.regions)) :=
      pairAll_total_eq (G := fun x => 0 < x.mass) (fun _ _ ha hb => ⟨ha, hb⟩)
        (fun _ _ _ _ => rfl) _ (by
          intro x hx
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
          exact hl b hb)
    exact h1.trans (total_map_eq (f := accelerate w.laws w.regions) (fun _ => rfl) _)
  show total Body.mass (((collisionStage w.laws w.nextId (applyForces w)).1.map
    (limitSpeed w.laws)).map (moveBody w)) = _
  rw [total_map_eq (f := moveBody w) (fun b => by
      show w.laws.massRate * b.mass = b.mass
      rw [hr, one_mul]),
    total_map_eq (f := limitSpeed w.laws) (fun _ => rfl)]
  exact (collisionStage_mass w.laws hm w.nextId _ hforcedPos).trans hforced

end Paradox

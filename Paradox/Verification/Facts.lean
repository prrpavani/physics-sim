import Paradox.Physics.Kinematics
import Paradox.Invariants.Property

/-!
# Facts about one tick

Each stage of `tick` is handled by one lemma. `StageClosed` collects what a per-body fact must
satisfy to survive every collision mode, so the same proof covers all of them.
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

theorem pairOne_ids {f : Body → Body → Body × Body}
    (hf : ∀ a b, (f a b).1.id = a.id ∧ (f a b).2.id = b.id) (l : List Body) (a : Body) :
    (pairOne f a l).1.id = a.id ∧ (pairOne f a l).2.map Body.id = l.map Body.id := by
  induction l generalizing a with
  | nil => simp [pairOne]
  | cons c cs ih =>
    have r := ih (f a c).1
    refine ⟨r.1.trans (hf a c).1, ?_⟩
    simp only [pairOne, List.map_cons]
    rw [(hf a c).2, r.2]

theorem pairAll_ids {f : Body → Body → Body × Body}
    (hf : ∀ a b, (f a b).1.id = a.id ∧ (f a b).2.id = b.id) (l : List Body) :
    (pairAll f l).map Body.id = l.map Body.id := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    have r := pairOne_ids hf (pairAll f bs) b
    simp only [pairAll, List.map_cons]
    rw [r.1, r.2, ih]

/-! ## Facts that survive every collision mode -/

/-- A fact about a single body that no collision mode can break. -/
structure StageClosed (Q : Body → Prop) : Prop where
  velocity : ∀ (b : Body) v, Q b → Q { b with velocity := v }
  swapMass : ∀ a b : Body, Q a → Q b → Q { a with mass := b.mass }
  merge : ∀ a b, Q a → Q b → Q (mergeBodies a b)
  child : ∀ id a b, Q a → Q b → Q (childOf id a b)

theorem mergeOne_forall {Q : Body → Prop} (hc : StageClosed Q) (l : List Body) (a : Body)
    (ha : Q a) (hl : ∀ x ∈ l, Q x) : ∀ x ∈ mergeOne a l, Q x := by
  induction l with
  | nil => simpa [mergeOne] using ha
  | cons c cs ih =>
    intro x hx
    simp only [mergeOne] at hx
    split at hx
    · rcases List.mem_cons.mp hx with rfl | h
      · exact hc.merge a c ha (hl c List.mem_cons_self)
      · exact hl x (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.mp hx with rfl | h
      · exact hl x List.mem_cons_self
      · exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) x h

theorem mergeAll_forall {Q : Body → Prop} (hc : StageClosed Q) (l : List Body)
    (hl : ∀ x ∈ l, Q x) : ∀ x ∈ mergeAll l, Q x := by
  induction l with
  | nil => simp [mergeAll]
  | cons b bs ih =>
    exact mergeOne_forall hc _ b (hl b List.mem_cons_self)
      (ih fun x hx => hl x (List.mem_cons_of_mem _ hx))

theorem firstTouchingPair_mem {l : List Body} {a b : Body}
    (h : firstTouchingPair l = some (a, b)) : a ∈ l ∧ b ∈ l := by
  induction l with
  | nil => simp [firstTouchingPair] at h
  | cons c cs ih =>
    simp only [firstTouchingPair] at h
    split at h
    next d hd =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ (List.mem_of_find?_eq_some hd)⟩
    next =>
      obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

theorem collisionStage_forall {Q : Body → Prop} (hc : StageClosed Q) (laws : PhysicsLaws)
    (nextId : Nat) (l : List Body) (hl : ∀ x ∈ l, Q x) :
    ∀ x ∈ (collisionStage laws nextId l).1, Q x := by
  unfold collisionStage
  split
  · exact hl
  · refine pairAll_forall (fun a b ha hb => ?_) l hl
    unfold bouncePair
    dsimp only
    split
    · exact ⟨hc.velocity _ _ ha, hc.velocity _ _ hb⟩
    · exact ⟨ha, hb⟩
  · refine pairAll_forall (fun a b ha hb => ?_) l hl
    unfold exchangeVelocityPair
    split
    · exact ⟨hc.velocity _ _ ha, hc.velocity _ _ hb⟩
    · exact ⟨ha, hb⟩
  · refine pairAll_forall (fun a b ha hb => ?_) l hl
    unfold exchangeMassPair
    split
    · exact ⟨hc.swapMass _ _ ha hb, hc.swapMass _ _ hb ha⟩
    · exact ⟨ha, hb⟩
  · exact mergeAll_forall hc l hl
  · unfold spawnStage
    split
    · split
      next a b hp =>
        obtain ⟨h1, h2⟩ := firstTouchingPair_mem hp
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hl x h
        · rw [List.mem_singleton] at h
          subst h
          exact hc.child _ a b (hl a h1) (hl b h2)
      next => exact hl
    · exact hl

/-- A per-body fact closed under collisions survives the forces and collisions of a tick. -/
theorem forces_collisions_forall {Q : Body → Prop} (hc : StageClosed Q) (w : World)
    (hl : ∀ x ∈ w.bodies, Q x) :
    ∀ x ∈ (collisionStage w.laws w.nextId (applyForces w)).1, Q x := by
  refine collisionStage_forall hc _ _ _ ?_
  refine pairAll_forall (fun a b ha hb => ⟨hc.velocity a _ ha, hc.velocity b _ hb⟩) _ ?_
  intro x hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact hc.velocity _ _ (hl b hb)

/-- Every body after a tick comes from a body after the collision stage. -/
theorem mem_tick {w : World} {b' : Body} (h : b' ∈ (tick w).bodies) :
    ∃ b ∈ (collisionStage w.laws w.nextId (applyForces w)).1,
      b' = moveBody w (limitSpeed w.laws b) := by
  have h' : b' ∈ ((collisionStage w.laws w.nextId (applyForces w)).1.map
      (limitSpeed w.laws)).map (moveBody w) := h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h'
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  exact ⟨b, hb, rfl⟩

/-! ## Fitting in the box -/

theorem fits_stageClosed (bounds : Bounds) : StageClosed (FitsIn bounds) where
  velocity _ _ h := h
  swapMass _ _ ha _ := ha
  merge a b ha hb := by
    unfold FitsIn Body.extent at *
    dsimp only [mergeBodies]
    split <;> assumption
  child _ _ _ ha _ := ha

/-- After a tick, every body still fits in the box. -/
theorem tick_fits {w : World} (h : ∀ b ∈ w.bodies, FitsIn w.bounds b) :
    ∀ b ∈ (tick w).bodies, FitsIn w.bounds b := by
  intro b' hb'
  obtain ⟨b, hb, rfl⟩ := mem_tick hb'
  exact forces_collisions_forall (fits_stageClosed _) w h b hb

/-! ## Positive mass -/

theorem positiveMass_stageClosed : StageClosed (fun b => 0 < b.mass) where
  velocity _ _ h := h
  swapMass _ _ _ hb := hb
  merge _ _ ha hb := add_pos ha hb
  child _ _ _ ha hb := half_pos (add_pos ha hb)

/-- If the mass rate is positive, a tick keeps every mass positive. -/
theorem tick_positiveMass {w : World} (hr : 0 < w.laws.massRate) (h : PositiveMass w) :
    PositiveMass (tick w) := by
  intro b' hb'
  obtain ⟨b, hb, rfl⟩ := mem_tick hb'
  exact mul_pos hr (forces_collisions_forall positiveMass_stageClosed w h b hb)

/-! ## Bounded position -/

/-- After a tick, every body that fits is fully inside the world. -/
theorem tick_boundedPosition {w : World} (h : ∀ b ∈ w.bodies, FitsIn w.bounds b) :
    BoundedPosition (tick w) := by
  intro b' hb'
  obtain ⟨b, hb, rfl⟩ := mem_tick hb'
  have hfit := forces_collisions_forall (fits_stageClosed _) w h b hb
  exact Bounds.contains_clampPoint hfit.2 _

/-! ## Bounded velocity -/

/-- Moving a body never makes it faster along an axis, if a bounce cannot add speed. -/
theorem abs_moveAxis_snd_le (t : Topology) {e : ℚ} (dt lo hi p v : ℚ) (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    |(moveAxis t e dt lo hi p v).2| ≤ |v| := by
  have hb : |(-(e * v))| ≤ |v| := by
    rw [abs_neg, abs_mul, abs_of_nonneg h0]
    nlinarith [abs_nonneg v]
  unfold moveAxis
  cases t with
  | box =>
    dsimp only
    split
    · exact hb
    · split
      · exact hb
      · exact le_rfl
  | torus =>
    dsimp only
    split <;> exact le_rfl

theorem withinAbs_of_le {a b : Vec3} {m : ℚ} (h : b.WithinAbs m)
    (hx : |a.x| ≤ |b.x|) (hy : |a.y| ≤ |b.y|) (hz : |a.z| ≤ |b.z|) : a.WithinAbs m :=
  ⟨hx.trans h.1, hy.trans h.2.1, hz.trans h.2.2⟩

/-- A safe portal effect keeps a velocity within the limit. -/
theorem PortalEffect.apply_withinAbs {e : PortalEffect} (he : e.Safe) {v : Vec3} {m : ℚ}
    (h : v.WithinAbs m) : (e.apply v).WithinAbs m := by
  cases e with
  | none => exact h
  | reverse =>
    exact ⟨(abs_neg v.x).le.trans h.1, (abs_neg v.y).le.trans h.2.1, (abs_neg v.z).le.trans h.2.2⟩
  | rotate => exact ⟨h.2.2, h.2.1, (abs_neg v.x).le.trans h.1⟩
  | scale k =>
    have hk : |k| ≤ 1 := he
    have key : ∀ x : ℚ, |k * x| ≤ |x| := fun x => by
      rw [abs_mul]; nlinarith [abs_nonneg x]
    exact withinAbs_of_le h (key _) (key _) (key _)

theorem throughPortals_withinAbs {portals : List Portal} (hp : ∀ q ∈ portals, q.effect.Safe)
    (p : Vec3) {v : Vec3} {m : ℚ} (h : v.WithinAbs m) :
    (throughPortals portals p v).2.WithinAbs m := by
  unfold throughPortals
  split
  next q hq => exact PortalEffect.apply_withinAbs (hp q (List.mem_of_find?_eq_some hq)) h
  next => exact h

/-- Moving a body keeps its velocity within any limit it was already within. -/
theorem moveBody_withinAbs {w : World} {b : Body} {m : ℚ}
    (h0 : 0 ≤ w.laws.restitution) (h1 : w.laws.restitution ≤ 1)
    (hp : ∀ q ∈ w.portals, q.effect.Safe) (hv : b.velocity.WithinAbs m) :
    (moveBody w b).velocity.WithinAbs m := by
  unfold moveBody
  dsimp only
  refine withinAbs_of_le (throughPortals_withinAbs hp _ (withinAbs_of_le hv ?_ ?_ ?_))
    (abs_snap_le _ _) (abs_snap_le _ _) (abs_snap_le _ _)
  all_goals exact abs_moveAxis_snd_le _ _ _ _ _ _ h0 h1

/-- After a tick, velocities respect the speed limit in a safe environment. -/
theorem tick_boundedVelocity {w : World} (hm : 0 ≤ w.laws.maxSpeed)
    (h0 : 0 ≤ w.laws.restitution) (h1 : w.laws.restitution ≤ 1)
    (hp : ∀ q ∈ w.portals, q.effect.Safe) : BoundedVelocity (tick w) := by
  intro b' hb'
  obtain ⟨b, -, rfl⟩ := mem_tick hb'
  exact moveBody_withinAbs h0 h1 hp (Vec3.withinAbs_clampAbs _ hm)

/-! ## Unique ids -/

theorem mergeOne_ids (a : Body) (l : List Body) :
    ∀ x ∈ (mergeOne a l).map Body.id, x = a.id ∨ x ∈ l.map Body.id := by
  induction l with
  | nil => simp [mergeOne]
  | cons c cs ih =>
    intro x hx
    simp only [mergeOne] at hx
    split at hx
    · simp only [List.map_cons, List.mem_cons] at hx ⊢
      rcases hx with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (Or.inr h)
    · simp only [List.map_cons, List.mem_cons] at hx ⊢
      rcases hx with rfl | h
      · exact Or.inr (Or.inl rfl)
      · rcases ih x h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr h')

theorem mergeOne_nodup (a : Body) (l : List Body) (ha : a.id ∉ l.map Body.id)
    (hl : (l.map Body.id).Nodup) : ((mergeOne a l).map Body.id).Nodup := by
  induction l with
  | nil => simp [mergeOne]
  | cons c cs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hl ha
    simp only [mergeOne]
    split
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨ha.2, hl.2⟩
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => ?_, ih ha.2 hl.2⟩
      rcases mergeOne_ids a cs c.id hmem with h | h
      · exact ha.1 h.symm
      · exact hl.1 h

theorem mergeAll_ids (l : List Body) :
    ∀ x ∈ (mergeAll l).map Body.id, x ∈ l.map Body.id := by
  induction l with
  | nil => simp [mergeAll]
  | cons b bs ih =>
    intro x hx
    rcases mergeOne_ids b (mergeAll bs) x hx with h | h
    · simp [h]
    · simp only [List.map_cons, List.mem_cons]
      exact Or.inr (ih x h)

theorem mergeAll_nodup (l : List Body) (hl : (l.map Body.id).Nodup) :
    ((mergeAll l).map Body.id).Nodup := by
  induction l with
  | nil => simp [mergeAll]
  | cons b bs ih =>
    simp only [List.map_cons, List.nodup_cons] at hl
    exact mergeOne_nodup b _ (fun h => hl.1 (mergeAll_ids bs _ h)) (ih hl.2)

/-- The collision stage keeps ids unique and below the next free id. -/
theorem collisionStage_ids (laws : PhysicsLaws) (nextId : Nat) (l : List Body)
    (hl : (l.map Body.id).Nodup) (hb : ∀ b ∈ l, b.id < nextId) :
    ((collisionStage laws nextId l).1.map Body.id).Nodup ∧
      ∀ b ∈ (collisionStage laws nextId l).1, b.id < (collisionStage laws nextId l).2 := by
  have pairCase : ∀ f : Body → Body → Body × Body,
      (∀ a b, (f a b).1.id = a.id ∧ (f a b).2.id = b.id) →
      ((pairAll f l).map Body.id).Nodup ∧ ∀ b ∈ pairAll f l, b.id < nextId := by
    intro f hf
    have hids := pairAll_ids hf l
    refine ⟨hids ▸ hl, fun b hb' => ?_⟩
    have : b.id ∈ l.map Body.id := hids ▸ List.mem_map_of_mem hb'
    obtain ⟨c, hc, he⟩ := List.mem_map.mp this
    exact he ▸ hb c hc
  unfold collisionStage
  split
  · exact ⟨hl, hb⟩
  · refine pairCase _ fun a b => ?_
    unfold bouncePair
    dsimp only
    split <;> exact ⟨rfl, rfl⟩
  · refine pairCase _ fun a b => ?_
    unfold exchangeVelocityPair
    split <;> exact ⟨rfl, rfl⟩
  · refine pairCase _ fun a b => ?_
    unfold exchangeMassPair
    split <;> exact ⟨rfl, rfl⟩
  · refine ⟨mergeAll_nodup l hl, fun b hb' => ?_⟩
    have := mergeAll_ids l b.id (List.mem_map_of_mem hb')
    obtain ⟨c, hc, he⟩ := List.mem_map.mp this
    exact he ▸ hb c hc
  · unfold spawnStage
    split
    · split
      · refine ⟨?_, fun b hb' => ?_⟩
        · simp only [List.map_append, List.map_cons, List.map_nil]
          refine List.nodup_append.mpr ⟨hl, by simp, ?_⟩
          intro x hx y hy
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
          simp only [List.mem_singleton] at hy
          subst hy
          exact Nat.ne_of_lt (hb c hc)
        · rcases List.mem_append.mp hb' with h | h
          · exact Nat.lt_succ_of_lt (hb b h)
          · rw [List.mem_singleton] at h
            subst h
            exact Nat.lt_succ_self _
      · exact ⟨hl, hb⟩
    · exact ⟨hl, hb⟩

/-- A tick keeps ids unique and below the next free id. -/
theorem tick_uniqueIds {w : World} (h : UniqueIds w) : UniqueIds (tick w) := by
  have hforce : (applyForces w).map Body.id = w.bodies.map Body.id := by
    unfold applyForces
    rw [pairAll_ids (fun _ _ => ⟨rfl, rfl⟩), List.map_map]
    rfl
  have hstage := collisionStage_ids w.laws w.nextId (applyForces w) (hforce ▸ h.1) (by
    intro b hb
    have : b.id ∈ w.bodies.map Body.id := hforce ▸ List.mem_map_of_mem hb
    obtain ⟨c, hc, he⟩ := List.mem_map.mp this
    exact he ▸ h.2 c hc)
  constructor
  · show ((((collisionStage w.laws w.nextId (applyForces w)).1.map
      (limitSpeed w.laws)).map (moveBody w)).map Body.id).Nodup
    rw [List.map_map, List.map_map]
    exact hstage.1
  · intro b' hb'
    obtain ⟨b, hb, rfl⟩ := mem_tick hb'
    exact hstage.2 b hb

end Paradox

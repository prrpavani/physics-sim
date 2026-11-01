import Paradox.Engine.System
import Paradox.Rules.Events
import Paradox.Verification.RuleSoundness

/-!
# Evolution consistency for the physics domain

Each guarantee is carried by `Inv`: the guarantee holds, the environment is safe, and every rule in
the world has passed the rule checker for that guarantee. `step_inv` shows one permitted event keeps
`Inv` true. The generic engine then gives the result for every finite list of events.
-/

namespace Paradox

open Engine

/-- The guarantee `p` holds, the environment is safe, and all rules are checked for `p`. -/
def Inv (p : Property) (w : World) : Prop :=
  SafeEnvironment w ∧ p.holds w ∧ ∀ r ∈ w.rules, r.envSafe = true ∧ r.keeps p = true

/-- Every guarantee at once. -/
def Guaranteed (w : World) : Prop :=
  ∀ p, Inv p w

instance (p : Property) (w : World) : Decidable (Inv p w) := by unfold Inv; infer_instance

instance (w : World) : Decidable (Guaranteed w) :=
  decidable_of_iff (∀ p ∈ Property.all, Inv p w)
    ⟨fun h p => h p (Property.mem_all p), fun h p _ => h p⟩

instance (w : World) (es : List EnvironmentEvent) :
    Decidable (AllowedTrace step Allowed w es) := by
  induction es generalizing w with
  | nil => exact isTrue trivial
  | cons e es ih =>
    have := ih (step w e)
    unfold AllowedTrace
    infer_instance

/-! ## What events do -/

theorem updateBody_forall {Q : Body → Prop} {id : Nat} {f : Body → Body} {l : List Body}
    (hl : ∀ b ∈ l, Q b) (hf : ∀ b, Q b → Q (f b)) : ∀ b ∈ updateBody id f l, Q b := by
  intro x hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  split
  · exact hf b (hl b hb)
  · exact hl b hb

theorem updateBody_ids {id : Nat} {f : Body → Body} (hf : ∀ b, (f b).id = b.id) (l : List Body) :
    (updateBody id f l).map Body.id = l.map Body.id := by
  unfold updateBody
  rw [List.map_map]
  refine List.map_congr_left fun b _ => ?_
  dsimp only [Function.comp]
  split
  · exact hf b
  · rfl

/-- A permitted event keeps the environment safe. -/
theorem applyEvent_safe {w : World} {e : EnvironmentEvent} (ha : Allowed w e)
    (h : SafeEnvironment w) : SafeEnvironment (applyEvent w e) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  cases e <;> try exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  case changeMaxSpeed v => exact ⟨h1, ha, h3, h4, h5, h6, h7, h8, h9⟩
  case changeMaxAcceleration a => exact ⟨h1, h2, ha, h4, h5, h6, h7, h8, h9⟩
  case changeRestitution r => exact ⟨h1, h2, h3, h4, ha, h6, h7, h8, h9⟩
  case changeTimeStep dt => exact ⟨h1, h2, h3, ha, h5, h6, h7, h8, h9⟩
  case changeBounds b => exact ⟨ha.1, h2, h3, h4, h5, h6, h7, h8, ha.2⟩
  case setMassRate r => exact ⟨h1, h2, h3, h4, h5, ha, h7, h8, h9⟩
  case reverseTime =>
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun x hx => ?_⟩
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact h9 b hb
  case spawnBody b =>
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun x hx => ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact h9 x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact ha.1
  case removeBody id =>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun x hx => h9 x (List.mem_of_mem_filter hx)⟩
  case applyImpulse id dv =>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, updateBody_forall h9 fun _ hb => hb⟩
  case setBodyState id p v =>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, updateBody_forall h9 fun _ hb => hb⟩
  case addRegion r =>
    refine ⟨h1, h2, h3, h4, h5, h6, h7, fun x hx => ?_, h9⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact h8 x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact ha
  case clearRegions => exact ⟨h1, h2, h3, h4, h5, h6, h7, by simp [applyEvent], h9⟩
  case addPortal p =>
    refine ⟨h1, h2, h3, h4, h5, h6, fun x hx => ?_, h8, h9⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact h7 x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact ha
  case clearPortals => exact ⟨h1, h2, h3, h4, h5, h6, by simp [applyEvent], h8, h9⟩

/-- A permitted event keeps every mass positive. -/
theorem applyEvent_positiveMass {w : World} {e : EnvironmentEvent} (ha : Allowed w e)
    (h : PositiveMass w) : PositiveMass (applyEvent w e) := by
  cases e <;> try exact h
  case reverseTime =>
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact h b hb
  case spawnBody b =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact ha.2.1
  case removeBody id => exact fun x hx => h x (List.mem_of_mem_filter hx)
  case applyImpulse id dv => exact updateBody_forall h fun _ hb => hb
  case setBodyState id p v => exact updateBody_forall h fun _ hb => hb

/-- A permitted event keeps ids unique and below the next free id. -/
theorem applyEvent_uniqueIds {w : World} {e : EnvironmentEvent} (ha : Allowed w e)
    (h : UniqueIds w) : UniqueIds (applyEvent w e) := by
  cases e <;> try exact h
  case reverseTime =>
    refine ⟨?_, fun x hx => ?_⟩
    · show ((w.bodies.map fun b => { b with velocity := b.velocity.neg }).map Body.id).Nodup
      rw [List.map_map]
      exact h.1
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact h.2 b hb
  case spawnBody b =>
    refine ⟨?_, fun x hx => ?_⟩
    · show ((w.bodies ++ [b]).map Body.id).Nodup
      simp only [List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.mpr ⟨h.1, by simp, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      exact fun heq => ha.2.2.1 (heq ▸ hx)
    · show x.id < max w.nextId (b.id + 1)
      rcases List.mem_append.mp hx with hx | hx
      · exact lt_of_lt_of_le (h.2 x hx) (le_max_left _ _)
      · rw [List.mem_singleton] at hx
        subst hx
        exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  case removeBody id =>
    refine ⟨(List.Sublist.map _ List.filter_sublist).nodup h.1, ?_⟩
    exact fun x hx => h.2 x (List.mem_of_mem_filter hx)
  case applyImpulse id dv =>
    refine ⟨?_, updateBody_forall h.2 fun _ hb => hb⟩
    have hids := updateBody_ids (id := id)
      (f := fun b => { b with velocity := b.velocity.add dv }) (fun _ => rfl) w.bodies
    show ((updateBody id _ w.bodies).map Body.id).Nodup
    rw [hids]
    exact h.1
  case setBodyState id p v =>
    refine ⟨?_, updateBody_forall h.2 fun _ hb => hb⟩
    have hids := updateBody_ids (id := id)
      (f := fun b => { b with position := p, velocity := v }) (fun _ => rfl) w.bodies
    show ((updateBody id _ w.bodies).map Body.id).Nodup
    rw [hids]
    exact h.1

/-- A permitted event keeps the rule list checked. -/
theorem applyEvent_rules {w : World} {e : EnvironmentEvent} {p : Property} (ha : Allowed w e)
    (h : ∀ r ∈ w.rules, r.envSafe = true ∧ r.keeps p = true) :
    ∀ r ∈ (applyEvent w e).rules, r.envSafe = true ∧ r.keeps p = true := by
  cases e <;> try exact h
  case addRule r =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact Rule.certified_parts ha p
  case clearRules => simp [applyEvent]

/-! ## One tick -/

/-- A tick keeps the environment safe. -/
theorem tick_safe {w : World} (h : SafeEnvironment w) : SafeEnvironment (tick w) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, tick_fits h9⟩

/-! ## Theorem: one permitted event -/

/-- After applying the event and ticking, each guarantee holds in a safe environment. -/
theorem moved_holds {w : World} {e : EnvironmentEvent} {p : Property} (ha : Allowed w e)
    (he : SafeEnvironment w) (hp : p.holds w) :
    SafeEnvironment (tick (applyEvent w e)) ∧ p.holds (tick (applyEvent w e)) := by
  have he' := applyEvent_safe ha he
  refine ⟨tick_safe he', ?_⟩
  cases p with
  | positiveMass => exact tick_positiveMass he'.2.2.2.2.2.1 (applyEvent_positiveMass ha hp)
  | boundedPosition => exact tick_boundedPosition he'.2.2.2.2.2.2.2.2
  | boundedVelocity =>
    exact tick_boundedVelocity he'.2.1.le he'.2.2.2.2.1.1 he'.2.2.2.2.1.2 he'.2.2.2.2.2.2.1
  | safeEnvironment => exact tick_safe he'
  | uniqueIds => exact tick_uniqueIds (applyEvent_uniqueIds ha hp)

/-- **One permitted event keeps each guarantee.** -/
theorem step_inv (p : Property) : PreservesAll (Inv p) step Allowed := by
  rintro w e ⟨he, hp, hr⟩ ha
  have hr' := applyEvent_rules ha hr
  obtain ⟨he1, hp1⟩ := moved_holds ha he hp
  have hrules : ∀ r ∈ (tick (applyEvent w e)).rules, r.envSafe = true ∧ r.keeps p = true := hr'
  obtain ⟨he2, hp2⟩ := evalRules_sound w p _ _ hrules he1 hp1
  refine ⟨he2, hp2, ?_⟩
  show ∀ r ∈ (evalRules w (tick (applyEvent w e)).rules (tick (applyEvent w e))).rules, _
  rw [evalRules_rules]
  exact hrules

/-- **Finite sequences.** Starting from a world where the guarantee holds, it still holds after
any finite list of permitted events. -/
theorem run_inv (p : Property) (w : World) (events : List EnvironmentEvent)
    (hw : Inv p w) (htrace : AllowedTrace step Allowed w events) : Inv p (run w events) :=
  run_preserves (step_inv p) w events hw htrace

/-- **All guarantees together.** -/
theorem guaranteed_run (w : World) (events : List EnvironmentEvent)
    (hw : Guaranteed w) (htrace : AllowedTrace step Allowed w events) :
    Guaranteed (run w events) :=
  fun p => run_inv p w events (hw p) htrace

/-! ## Theorem: rules applied in any order -/

/-- One move where the world's rules may run in any order. -/
def Next (e : EnvironmentEvent) (w w' : World) : Prop :=
  ∃ order, order.Perm (applyEvent w e).rules ∧
    w' = evalRules w order (tick (applyEvent w e))

/-- **Order independence of guarantees.** Every possible next state keeps the guarantee, whatever
order the rules run in. Rules may disagree about the outcome, but not about this. -/
theorem next_inv (p : Property) (e : EnvironmentEvent) (w : World) (ha : Allowed w e)
    (hw : Inv p w) {w' : World} (hn : Next e w w') : Inv p w' := by
  obtain ⟨he, hp, hr⟩ := hw
  obtain ⟨order, hperm, rfl⟩ := hn
  have hr' := applyEvent_rules ha hr
  obtain ⟨he1, hp1⟩ := moved_holds ha he hp
  obtain ⟨he2, hp2⟩ := evalRules_sound w p order _
    (fun r hmem => hr' r (hperm.mem_iff.mp hmem)) he1 hp1
  refine ⟨he2, hp2, ?_⟩
  rw [evalRules_rules]
  exact hr'

/-! ## The limits of `Allowed` -/

/-- A negative speed limit breaks the velocity bound whenever at least one body exists after the
tick, so the velocity theorem cannot be widened to all events. -/
theorem negative_maxSpeed_violates {w : World} {v : ℚ} (hv : v < 0)
    (hb : (tick (applyEvent w (.changeMaxSpeed v))).bodies ≠ []) :
    ¬ BoundedVelocity (tick (applyEvent w (.changeMaxSpeed v))) := by
  intro h
  obtain ⟨b, hmem⟩ := List.exists_mem_of_ne_nil _ hb
  have : 0 ≤ v := (h b hmem).limit_nonneg
  linarith

end Paradox

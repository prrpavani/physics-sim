import Paradox.Rules.Events
import Paradox.Invariants.Mass
import Paradox.Invariants.Boundedness
import Paradox.Invariants.Speed
import Paradox.Invariants.Environment

/-!
# Preservation theorems

The generic part (`Preserves`, `PreservesAll`, composition, induction over event sequences) knows
nothing about physics. The rest instantiates it for the transition function `step`.
-/

namespace Paradox

/-! ## Generic preservation -/

/-- The transition `f` keeps `P` true. -/
def Preserves (P : World → Prop) (f : World → World) : Prop :=
  ∀ w, P w → P (f w)

/-- Every permitted event keeps `P` true. -/
def PreservesAll
    (P : World → Prop)
    (transition : World → EnvironmentEvent → World)
    (allowed : World → EnvironmentEvent → Prop) : Prop :=
  ∀ w e, P w → allowed w e → P (transition w e)

/-- Running `f` and then `g` preserves whatever both preserve. -/
theorem Preserves.comp {P : World → Prop} {f g : World → World}
    (hg : Preserves P g) (hf : Preserves P f) : Preserves P (g ∘ f) :=
  fun w hw => hg (f w) (hf w hw)

/-- Every event in the list is permitted in the state the earlier events produced. -/
def AllowedTrace (allowed : World → EnvironmentEvent → Prop) :
    World → List EnvironmentEvent → Prop
  | _, [] => True
  | w, e :: es => allowed w e ∧ AllowedTrace allowed (step w e) es

instance (w : World) (es : List EnvironmentEvent) : Decidable (AllowedTrace Allowed w es) := by
  induction es generalizing w with
  | nil => exact isTrue trivial
  | cons e es ih =>
    have := ih (step w e)
    unfold AllowedTrace
    infer_instance

/-- **Theorem 5.** An invariant preserved by each permitted event holds after any finite sequence
of permitted events. -/
theorem run_preserves {P : World → Prop} {allowed : World → EnvironmentEvent → Prop}
    (h : PreservesAll P step allowed) (w : World) (events : List EnvironmentEvent)
    (hw : P w) (htrace : AllowedTrace allowed w events) : P (run w events) := by
  induction events generalizing w with
  | nil => exact hw
  | cons e es ih => exact ih (step w e) (h w e hw htrace.1) htrace.2

/-! ## How `tick` and `applyEvent` act on bodies -/

theorem mem_tick_bodies {w : World} {b' : Body} (h : b' ∈ (tick w).bodies) :
    ∃ b ∈ w.bodies, b' = tickBody w.laws w.bounds b := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
  exact ⟨b, hb, rfl⟩

/-! ## Theorem 1: positive mass -/

theorem tick_preserves_positiveMass : Preserves PositiveMass tick := by
  intro w hw b' hb'
  obtain ⟨b, hb, rfl⟩ := mem_tick_bodies hb'
  exact hw b hb

theorem applyEvent_preserves_positiveMass (e : EnvironmentEvent) :
    Preserves PositiveMass (applyEvent · e) :=
  fun _ hw => hw

/-- Holds for every event, permitted or not. -/
theorem step_preserves_positiveMass (e : EnvironmentEvent) :
    Preserves PositiveMass (step · e) :=
  tick_preserves_positiveMass.comp (applyEvent_preserves_positiveMass e)

/-! ## Theorem 2: bounded position -/

theorem tick_preserves_boundedPosition : Preserves BoundedPosition tick := by
  intro w hw b' hb'
  obtain ⟨b, hb, rfl⟩ := mem_tick_bodies hb'
  exact Bounds.contains_clampPoint (hw b hb).valid _

theorem applyEvent_preserves_boundedPosition (e : EnvironmentEvent) :
    Preserves BoundedPosition (applyEvent · e) :=
  fun _ hw => hw

/-- Holds for every event, permitted or not, because no event changes the boundaries. -/
theorem step_preserves_boundedPosition (e : EnvironmentEvent) :
    Preserves BoundedPosition (step · e) :=
  tick_preserves_boundedPosition.comp (applyEvent_preserves_boundedPosition e)

/-! ## Theorem 3: bounded velocity

Unlike mass and position, this does not factor through `applyEvent`: lowering the speed limit
leaves bodies temporarily over it, and the velocity clamp in `tick` restores the bound. -/

/-- After a tick, velocities respect the speed limit, provided that limit is non-negative. -/
theorem tick_boundedVelocity {w : World} (hm : 0 ≤ w.laws.maxSpeed) : BoundedVelocity (tick w) := by
  intro b' hb'
  obtain ⟨b, -, rfl⟩ := mem_tick_bodies hb'
  exact Vec3.withinAbs_clampAbs _ hm

/-- A permitted event leaves a non-negative speed limit non-negative. -/
theorem allowed_maxSpeed_nonneg {w : World} {e : EnvironmentEvent}
    (hm : 0 ≤ w.laws.maxSpeed) (he : Allowed w e) : 0 ≤ (applyEvent w e).laws.maxSpeed := by
  cases e with
  | changeMaxSpeed v => exact le_of_lt he
  | _ => exact hm

/-! ## Theorem 4: preservation across every permitted event -/

theorem positiveMass_preservesAll : PreservesAll PositiveMass step Allowed :=
  fun w e hw _ => step_preserves_positiveMass e w hw

theorem boundedPosition_preservesAll : PreservesAll BoundedPosition step Allowed :=
  fun w e hw _ => step_preserves_boundedPosition e w hw

theorem boundedVelocity_preservesAll : PreservesAll BoundedVelocity step Allowed := by
  intro w e hw he b' hb'
  obtain ⟨b, hb, -⟩ := mem_tick_bodies hb'
  exact tick_boundedVelocity (allowed_maxSpeed_nonneg (hw b hb).limit_nonneg he) b' hb'

theorem safeEnvironment_preservesAll : PreservesAll SafeEnvironment step Allowed := by
  rintro w e ⟨hb, hs, ha, ht⟩ he
  cases e with
  | changeMaxSpeed v => exact ⟨hb, he, ha, ht⟩
  | changeMaxAcceleration a => exact ⟨hb, hs, he, ht⟩
  | _ => exact ⟨hb, hs, ha, ht⟩

/-- All four invariants at once. -/
def Guaranteed (w : World) : Prop :=
  PositiveMass w ∧ BoundedPosition w ∧ BoundedVelocity w ∧ SafeEnvironment w

theorem guaranteed_preservesAll : PreservesAll Guaranteed step Allowed :=
  fun w e ⟨hm, hp, hv, hs⟩ he =>
    ⟨positiveMass_preservesAll w e hm he,
     boundedPosition_preservesAll w e hp he,
     boundedVelocity_preservesAll w e hv he,
     safeEnvironment_preservesAll w e hs he⟩

/-- **The central result so far.** A world satisfying all four invariants still satisfies them
after any finite sequence of permitted events. -/
theorem guaranteed_run (w : World) (events : List EnvironmentEvent)
    (hw : Guaranteed w) (htrace : AllowedTrace Allowed w events) : Guaranteed (run w events) :=
  run_preserves guaranteed_preservesAll w events hw htrace

/-! ## `Allowed` is necessary -/

/-- A negative speed limit breaks the velocity bound whenever at least one body exists, so the
velocity theorem cannot be strengthened to cover all events. -/
theorem negative_maxSpeed_violates_boundedVelocity (w : World) {v : ℚ}
    (hv : v < 0) (hbodies : w.bodies ≠ []) :
    ¬ BoundedVelocity (step w (.changeMaxSpeed v)) := by
  intro h
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ hbodies
  have hmem : tickBody (applyEvent w (.changeMaxSpeed v)).laws w.bounds b ∈
      (step w (.changeMaxSpeed v)).bodies :=
    List.mem_map.mpr ⟨b, hb, rfl⟩
  have hlimit : 0 ≤ v := (h _ hmem).limit_nonneg
  linarith

end Paradox

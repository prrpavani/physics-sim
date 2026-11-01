import Paradox.Verification.Verdict

/-!
# Protected and unprotected universes

A protected universe checks every event before it happens. It accepts the event, replaces it with a
safe version, or rejects it. `protectedRun_safe` is the headline result: from a safe start, no list
of events can break a guarantee, with no assumption about what the events are.
-/

namespace Paradox

/-- The safe version of an event, when one exists. -/
def repairEvent (w : World) : EnvironmentEvent → Option EnvironmentEvent
  | .changeRestitution e => some (.changeRestitution (max 0 (min e 1)))
  | .changeMaxAcceleration a => some (.changeMaxAcceleration (max 0 a))
  | .addPortal p =>
    match p.effect with
    | .scale k => some (.addPortal { p with effect := .scale (max (-1) (min k 1)) })
    | _ => none
  | .addRegion r => some (.addRegion { r with timeScale := max 0 r.timeScale })
  | .spawnBody b =>
    some (.spawnBody { b with
      position := (w.bounds.inset b.extent).clampPoint b.position
      velocity := b.velocity.clampAbs w.laws.maxSpeed })
  | .addRule r => r.repair.map .addRule
  | _ => none

/-- What protected mode did with an event. -/
inductive Decision where
  | accepted (e : EnvironmentEvent)
  /-- The event was replaced by this safe version. -/
  | repaired (original safe : EnvironmentEvent)
  | rejected (e : EnvironmentEvent)
  deriving DecidableEq, Repr

/-- Decide what to do with an event. Nothing is accepted without passing `Allowed`. -/
def decideEvent (w : World) (e : EnvironmentEvent) : Decision :=
  if Allowed w e then .accepted e
  else match repairEvent w e with
    | some e' => if Allowed w e' then .repaired e e' else .rejected e
    | none => .rejected e

/-- One protected step: the new world and what was decided. A rejected event still lets time pass,
as if nothing had happened. -/
def protectedStep (w : World) (e : EnvironmentEvent) : World × Decision :=
  let d := decideEvent w e
  match d with
  | .accepted e' => (step w e', d)
  | .repaired _ e' => (step w e', d)
  | .rejected _ => (step w .idle, d)

/-- The event that really runs is always permitted. -/
theorem protectedStep_allowed (w : World) (e : EnvironmentEvent) :
    ∃ e', (protectedStep w e).1 = step w e' ∧ Allowed w e' := by
  unfold protectedStep decideEvent
  split
  next ha => exact ⟨e, rfl, ha⟩
  next =>
    split
    next e' _ =>
      split
      next ha => exact ⟨e', rfl, ha⟩
      next => exact ⟨.idle, rfl, trivial⟩
    next => exact ⟨.idle, rfl, trivial⟩

/-- A protected step keeps each guarantee, for any event at all. -/
theorem protectedStep_inv (p : Property) (w : World) (e : EnvironmentEvent) (h : Inv p w) :
    Inv p (protectedStep w e).1 := by
  obtain ⟨e', he, ha⟩ := protectedStep_allowed w e
  rw [he]
  exact step_inv p w e' h ha

/-- Run a list of events in protected mode. -/
def protectedRun (w : World) (events : List EnvironmentEvent) : World :=
  events.foldl (fun current e => (protectedStep current e).1) w

/-- **A universe that cannot be broken.** From a world where a guarantee holds, the guarantee still
holds after any list of events in protected mode. There is no condition on the events. -/
theorem protectedRun_safe (p : Property) (w : World) (events : List EnvironmentEvent)
    (h : Inv p w) : Inv p (protectedRun w events) := by
  induction events generalizing w with
  | nil => exact h
  | cons e es ih => exact ih _ (protectedStep_inv p w e h)

/-- All guarantees survive any list of events in protected mode. -/
theorem protectedRun_guaranteed (w : World) (events : List EnvironmentEvent) (h : Guaranteed w) :
    Guaranteed (protectedRun w events) :=
  fun p => protectedRun_safe p w events (h p)

/-! ## User constraints, by enforcement -/

/-- A protected step that also refuses to make any of the user's constraints false. If the result
would break one, the world stays as it was and time does not pass. -/
def enforcedStep (cs : List Constraint) (w : World) (e : EnvironmentEvent) : World :=
  Engine.guard (fun v => ∀ c ∈ cs, c.holds v) (fun v => (protectedStep v e).1) w

/-- Run a list of events with constraints enforced. -/
def enforcedRun (cs : List Constraint) (w : World) (events : List EnvironmentEvent) : World :=
  events.foldl (enforcedStep cs) w

/-- **Any constraint can be enforced.** From a world meeting the constraints, they hold after any
list of events. Note what this says: the universe refuses changes that would break them, even if
that freezes it. It does not say the laws would have kept them on their own. -/
theorem enforcedRun_holds (cs : List Constraint) (w : World) (events : List EnvironmentEvent)
    (h : ∀ c ∈ cs, c.holds w) : ∀ c ∈ cs, c.holds (enforcedRun cs w events) := by
  induction events generalizing w with
  | nil => exact h
  | cons e es ih =>
    exact ih _ (Engine.guard_preserves (fun v => ∀ c ∈ cs, c.holds v) _ w h)

/-- Enforcing constraints never gives up the built-in guarantees. -/
theorem enforcedRun_inv (cs : List Constraint) (p : Property) (w : World)
    (events : List EnvironmentEvent) (h : Inv p w) : Inv p (enforcedRun cs w events) := by
  induction events generalizing w with
  | nil => exact h
  | cons e es ih =>
    refine ih _ ?_
    unfold enforcedStep Engine.guard
    split
    · exact protectedStep_inv p w e h
    · exact h

end Paradox

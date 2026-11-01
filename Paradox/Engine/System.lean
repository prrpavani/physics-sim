/-!
# The generic rule engine

Nothing here knows about physics. A universe is a type of states, a way to change state, and the
constraints it should obey. Each result below works for any such universe, so a new domain gets them
for free.
-/

namespace Paradox.Engine

variable {S E : Type}

/-! ## Rule consistency: can the constraints be met at all? -/

/-- At least one state meets the constraints. -/
def Satisfiable (Valid : S → Prop) : Prop :=
  ∃ s, Valid s

/-- One state that meets the constraints is enough to show they can be met. -/
theorem satisfiable_of_witness {Valid : S → Prop} (s : S) (h : Valid s) : Satisfiable Valid :=
  ⟨s, h⟩

/-! ## Evolution consistency, for one change -/

/-- The change `f` keeps `P` true. -/
def Preserves (P : S → Prop) (f : S → S) : Prop :=
  ∀ s, P s → P (f s)

/-- Doing `f` and then `g` keeps true whatever both keep true. -/
theorem preserves_comp {P : S → Prop} {f g : S → S}
    (hf : Preserves P f) (hg : Preserves P g) : Preserves P (g ∘ f) :=
  fun s hs => hg (f s) (hf s hs)

/-- Every permitted event keeps `P` true. -/
def PreservesAll (P : S → Prop) (step : S → E → S) (allowed : S → E → Prop) : Prop :=
  ∀ s e, P s → allowed s e → P (step s e)

/-! ## Evolution consistency, for many changes -/

/-- Run a list of events in order. -/
def runEvents (step : S → E → S) (s : S) (events : List E) : S :=
  events.foldl step s

/-- Every event in the list is permitted in the state the earlier events produced. -/
def AllowedTrace (step : S → E → S) (allowed : S → E → Prop) : S → List E → Prop
  | _, [] => True
  | s, e :: es => allowed s e ∧ AllowedTrace step allowed (step s e) es

/-- A property kept by each permitted event holds after any finite list of permitted events. -/
theorem run_preserves {P : S → Prop} {step : S → E → S} {allowed : S → E → Prop}
    (h : PreservesAll P step allowed) (s : S) (events : List E)
    (hs : P s) (htrace : AllowedTrace step allowed s events) : P (runEvents step s events) := by
  induction events generalizing s with
  | nil => exact hs
  | cons e es ih => exact ih (step s e) (h s e hs htrace.1) htrace.2

/-! ## Universes with more than one possible next state -/

/-- Every possible next state keeps `P` true. -/
def PreservesNext (P : S → Prop) (Next : S → S → Prop) : Prop :=
  ∀ s s', P s → Next s s' → P s'

/-- The states that can be reached from `start` in any number of moves. -/
inductive Reachable (Next : S → S → Prop) (start : S) : S → Prop where
  | start : Reachable Next start start
  | next {s s' : S} : Reachable Next start s → Next s s' → Reachable Next start s'

/-- A property kept by every move holds in every reachable state. -/
theorem reachable_preserves {P : S → Prop} {Next : S → S → Prop}
    (h : PreservesNext P Next) {start s : S} (hstart : P start)
    (hr : Reachable Next start s) : P s := by
  induction hr with
  | start => exact hstart
  | next _ hn ih => exact h _ _ ih hn

/-- There is only ever one possible next state. -/
def Deterministic (Next : S → S → Prop) : Prop :=
  ∀ s a b, Next s a → Next s b → a = b

/-- A universe that moves by a function is deterministic. -/
theorem deterministic_of_function (f : S → S) : Deterministic (fun s s' => s' = f s) :=
  fun _ _ _ ha hb => ha.trans hb.symm

/-! ## Guarantees by enforcement -/

/-- Make the change only if the result meets `P`. Otherwise stay in the same state. -/
def guard (P : S → Prop) [DecidablePred P] (f : S → S) (s : S) : S :=
  if P (f s) then f s else s

/-- A guarded change keeps `P` true, whatever `P` and `f` are. Note what this says: the universe
stops changes that would break `P`. It does not say that `f` itself is safe. -/
theorem guard_preserves (P : S → Prop) [DecidablePred P] (f : S → S) :
    Preserves P (guard P f) := by
  intro s hs
  unfold guard
  split
  · assumption
  · exact hs

/-! ## Counterexamples -/

/-- A claimed run: a start state, the events, and the state after each event. -/
structure Trace (S E : Type) where
  initial : S
  events : List E
  states : List S
  deriving Repr

/-- The state after a run, read from the trace. -/
def Trace.final (t : Trace S E) : S :=
  t.states.getLastD t.initial

/-- The states a real run produces. -/
def statesOf (step : S → E → S) : S → List E → List S
  | _, [] => []
  | s, e :: es => step s e :: statesOf step (step s e) es

/-- The states in a trace are exactly what the transition function produces. -/
def Trace.Replays (t : Trace S E) (step : S → E → S) : Prop :=
  t.states = statesOf step t.initial t.events

/-- The last state of a real run is the state after running all its events. -/
theorem statesOf_last (step : S → E → S) (s : S) (es : List E) :
    (statesOf step s es).getLastD s = runEvents step s es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    have := ih (step s e)
    cases hes : es with
    | nil => rfl
    | cons e' es' =>
      subst hes
      simpa [statesOf, runEvents, List.getLastD] using this

/-- A trace that replays and ends in a state breaking `P` shows the run truly breaks `P`. -/
theorem Trace.violates {t : Trace S E} {step : S → E → S} {P : S → Prop}
    (hreplay : t.Replays step) (hbad : ¬ P t.final) :
    ¬ P (runEvents step t.initial t.events) := by
  have : t.final = runEvents step t.initial t.events := by
    unfold Trace.final
    rw [hreplay]
    exact statesOf_last step t.initial t.events
  rwa [← this]

end Paradox.Engine

import Paradox.Proofs

/-!
# What the app reports

Each promise gets one of three answers, and each has a theorem behind it:

* **Proven:** `verdict_proven_sound` shows the promise holds at every future step.
* **Counterexample:** `checkTrace_sound` shows the run really happens and really breaks the promise.
* **Unproven:** neither was established. This never means false.
-/

namespace Paradox

/-! ## The promises as claims about a run -/

/-- The four promises. -/
inductive Promise where
  | staysInside
  | speedLimit
  | momentum
  | energy
  deriving DecidableEq, Repr

/-- What each promise says about a run from `start` to `final`. -/
def Promise.Holds : Promise → World → World → Prop
  | .staysInside, _, final => StaysInside final
  | .speedLimit, _, final => WithinSpeedLimit final
  | .momentum, _, final => MomentumKept final
  | .energy, start, final => totalEnergy final.bodies ≤ totalEnergy start.bodies

instance (p : Promise) (s f : World) : Decidable (p.Holds s f) := by
  cases p <;> unfold Promise.Holds <;> infer_instance

/-- The laws that keep each promise. -/
def Promise.Safe : Promise → Laws → Prop
  | .staysInside, _ => True
  | .speedLimit, l => SpeedSafe l
  | .momentum, l => MomentumSafe l
  | .energy, l => EnergySafe l

instance (p : Promise) (l : Laws) : Decidable (p.Safe l) := by
  cases p <;> unfold Promise.Safe <;> infer_instance

/-! ## Checking a counterexample -/

/-- A claimed run: where it starts and the state after each step. -/
structure Trace where
  start : World
  states : List World
  deriving DecidableEq, Repr

/-- The last state of a trace. -/
def Trace.final (t : Trace) : World :=
  t.states.getLastD t.start

/-- The states a real run of `n` steps produces. -/
def trajectory : Nat → World → List World
  | 0, _ => []
  | n + 1, w => tick w :: trajectory n (tick w)

theorem trajectory_last (n : Nat) (w : World) : (trajectory n w).getLastD w = run n w := by
  induction n generalizing w with
  | zero => rfl
  | succ k ih =>
    have := ih (tick w)
    cases k with
    | zero => rfl
    | succ j => simpa [trajectory, run, List.getLastD] using this

/-- A fair starting point: a valid universe where the promises it could break hold now. -/
def FairStart (w : World) : Prop :=
  WellFormed w ∧ StaysInside w ∧ WithinSpeedLimit w

instance (w : World) : Decidable (FairStart w) := by unfold FairStart; infer_instance

/-- Replay a trace through `tick` and check that it breaks the promise, from a fair start. Only this
turns a trace into evidence. -/
def checkTrace (p : Promise) (t : Trace) : Bool :=
  decide (FairStart t.start) &&
  decide (t.states = trajectory t.states.length t.start) &&
  decide (¬ p.Holds t.start t.final)

/-- **A checked counterexample is real.** It starts from a valid universe, and running the real step
function really breaks the promise. -/
theorem checkTrace_sound {p : Promise} {t : Trace} (h : checkTrace p t = true) :
    FairStart t.start ∧ ¬ p.Holds t.start (run t.states.length t.start) := by
  simp only [checkTrace, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hfair, hreplay⟩, hbad⟩ := h
  refine ⟨hfair, ?_⟩
  have hfinal : t.final = run t.states.length t.start := by
    unfold Trace.final
    conv_lhs => rw [hreplay]
    exact trajectory_last _ _
  rwa [hfinal] at hbad

/-! ## Searching for a counterexample -/

/-- A small test universe under the same laws: one object at the speed limit touching a wall, and one
more in the middle. It exposes laws that break a promise even if the current objects do not show it. -/
def probeWorld (w : World) : World :=
  let b := w.bounds
  let m := w.laws.maxSpeed
  { w with
    bodies :=
      [ { id := 0, position := ⟨b.maxX - 1 / 2, (b.minY + b.maxY) / 2, (b.minZ + b.maxZ) / 2⟩,
          velocity := ⟨m, 0, 0⟩, mass := 1, radius := 1 / 2 },
        { id := 1, position := ⟨(b.minX + b.maxX) / 2, (b.minY + b.maxY) / 2, (b.minZ + b.maxZ) / 2⟩,
          velocity := ⟨0, 1, 0⟩, mass := 2, radius := 1 / 2 } ]
    tick := 0 }

/-- The states up to the first one that breaks the promise, looking at most `n` steps ahead. -/
def firstBreak (p : Promise) (start : World) : Nat → World → List World → Option (List World)
  | 0, _, _ => none
  | n + 1, current, seen =>
    let next := tick current
    if p.Holds start next then firstBreak p start n next (next :: seen)
    else some (next :: seen).reverse

/-- Try one starting point. -/
def tryStart (p : Promise) (limit : Nat) (start : World) : Option Trace :=
  if FairStart start then
    match firstBreak p start limit start [] with
    | some states =>
      let t : Trace := ⟨start, states⟩
      if checkTrace p t then some t else none
    | none => none
  else none

/-- Search the current universe, then the test universe. Finding nothing proves nothing. -/
def findCounterexample (p : Promise) (limit : Nat) (w : World) : Option Trace :=
  match tryStart p limit w with
  | some t => some t
  | none => tryStart p limit (probeWorld w)

/-- **Everything the search returns has passed the checker.** -/
theorem findCounterexample_sound {p : Promise} {limit : Nat} {w : World} {t : Trace}
    (h : findCounterexample p limit w = some t) : checkTrace p t = true := by
  have key : ∀ s u, tryStart p limit s = some u → checkTrace p u = true := by
    intro s u hs
    unfold tryStart at hs
    split at hs
    · split at hs
      · dsimp only at hs
        split at hs
        next hc =>
          simp only [Option.some.injEq] at hs
          exact hs ▸ hc
        next => simp at hs
      · simp at hs
    · simp at hs
  unfold findCounterexample at h
  split at h
  next t' ht' =>
    simp only [Option.some.injEq] at h
    exact h ▸ key _ _ ht'
  next => exact key _ _ h

/-! ## Verdicts -/

/-- The answer for a promise. -/
inductive Status where
  | proven
  | counterexample
  | unproven
  deriving DecidableEq, Repr

/-- How far ahead the search looks. -/
def searchSteps : Nat := 300

/-- The answer for a promise, with its counterexample if there is one. -/
def verdict (p : Promise) (w : World) : Status × Option Trace :=
  if WellFormed w ∧ p.Safe w.laws then (.proven, none)
  else match findCounterexample p searchSteps w with
    | some t => (.counterexample, some t)
    | none => (.unproven, none)

/-- **A Proven card is correct.** If the app says Proven, the promise holds at every future step. -/
theorem verdict_proven_sound {p : Promise} {w : World} (h : (verdict p w).1 = .proven) (n : Nat) :
    p.Holds w (run (n + 1) w) := by
  unfold verdict at h
  split at h
  next hsafe =>
    obtain ⟨hw, hl⟩ := hsafe
    cases p with
    | staysInside => exact stays_inside_forever n (tick_wellFormed hw) (stays_inside hw)
    | speedLimit =>
      exact speedLimit_forever n (tick_wellFormed hw) hl (speedLimit_holds hw.1 hl)
    | momentum => exact momentum_forever (n + 1) hw hl
    | energy => exact energy_forever (n + 1) hw hl
  next =>
    split at h <;> simp at h

/-- **A counterexample on a card has passed the checker.** -/
theorem verdict_counterexample_sound {p : Promise} {w : World} {t : Trace}
    (h : (verdict p w).2 = some t) : checkTrace p t = true := by
  unfold verdict at h
  split at h
  · simp at h
  · split at h
    next t' ht' =>
      simp only [Option.some.injEq] at h
      exact h ▸ findCounterexample_sound ht'
    next => simp at h

/-! ## Keeping the universe consistent -/

/-- What the lock does with a change of laws. -/
inductive Decision where
  /-- The new laws keep the speed limit. -/
  | accepted (l : Laws)
  /-- The new laws would not. These are the same laws with the limiter turned on. -/
  | repaired (l : Laws)
  /-- The new laws are not meaningful, so nothing changes. -/
  | refused
  deriving DecidableEq, Repr

/-- Decide what to do with new laws. -/
def decideLaws (l : Laws) : Decision :=
  if LawsOk l then
    if SpeedSafe l then .accepted l else .repaired { l with limiter := true }
  else .refused

/-- The world after the lock decides. -/
def lockedSetLaws (w : World) (l : Laws) : World :=
  match decideLaws l with
  | .accepted a => { w with laws := a }
  | .repaired a => { w with laws := a }
  | .refused => w

/-- The lock keeps a world well-formed and speed safe. -/
theorem lockedSetLaws_ok {w : World} (hw : WellFormed w) (hs : SpeedSafe w.laws) (l : Laws) :
    WellFormed (lockedSetLaws w l) ∧ SpeedSafe (lockedSetLaws w l).laws := by
  unfold lockedSetLaws decideLaws
  by_cases hok : LawsOk l
  · by_cases hl : SpeedSafe l
    · simp only [if_pos hok, if_pos hl]
      exact ⟨⟨hok, hw.2⟩, hl⟩
    · simp only [if_pos hok, if_neg hl]
      exact ⟨⟨hok, hw.2⟩, Or.inl rfl⟩
  · simp only [if_neg hok]
    exact ⟨hw, hs⟩

/-- One step with the lock on: maybe a change of laws, then time passes. -/
def lockedStep (w : World) : Option Laws → World
  | some l => tick (lockedSetLaws w l)
  | none => tick w

/-- Run a list of steps with the lock on. -/
def lockedRun (w : World) (changes : List (Option Laws)) : World :=
  changes.foldl lockedStep w

/-- **With the lock on, nothing anyone does can break the speed limit.** From a valid world within the
limit, any list of law changes keeps it within the limit. -/
theorem locked_run_safe (w : World) (changes : List (Option Laws)) (hw : WellFormed w)
    (hs : SpeedSafe w.laws) (hv : WithinSpeedLimit w) : WithinSpeedLimit (lockedRun w changes) := by
  induction changes generalizing w with
  | nil => exact hv
  | cons c cs ih =>
    have key : WellFormed (lockedStep w c) ∧ SpeedSafe (lockedStep w c).laws ∧
        WithinSpeedLimit (lockedStep w c) := by
      cases c with
      | none => exact ⟨tick_wellFormed hw, hs, speedLimit_holds hw.1 hs⟩
      | some l =>
        obtain ⟨h1, h2⟩ := lockedSetLaws_ok hw hs l
        exact ⟨tick_wellFormed h1, h2, speedLimit_holds h1.1 h2⟩
    exact ih _ key.1 key.2.1 key.2.2

end Paradox

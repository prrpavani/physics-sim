import Paradox.Consistency.Constraints
import Paradox.Verification.Conservation

/-!
# Layer C: verdicts on what a universe guarantees

A verdict is one of a fixed set of statuses, and each has a theorem behind it:

* `proven`: `verifyProperty_proven` shows it holds across every permitted event sequence.
* `counterexample`: `checkTrace_sound` shows the trace really happens and really breaks the claim.
* `unknown`: neither was established. It never means "false".

Search only ever proposes traces. A trace counts only after `checkTrace` replays it through `step`.
-/

namespace Paradox

open Engine

/-! ## What can be claimed -/

/-- A claim about a run, comparing its start and end. -/
inductive Claim where
  /-- A built-in guarantee holds at the end. -/
  | property (p : Property)
  /-- A user's constraint holds at the end. -/
  | constraint (c : Constraint)
  /-- Total momentum along this direction is the same at the end. -/
  | momentumConserved (direction : Vec3)
  /-- Total kinetic energy is not larger at the end. -/
  | energyNotRising
  /-- Total mass is the same at the end. -/
  | massConserved
  /-- The number of objects is the same at the end. -/
  | populationConserved
  deriving DecidableEq, Repr

/-- What a claim says about a run from `start` to `final`. -/
def Claim.holds : Claim → World → World → Prop
  | .property p, _, final => p.holds final
  | .constraint c, _, final => c.holds final
  | .momentumConserved d, start, final =>
    totalMomentum d final.bodies = totalMomentum d start.bodies
  | .energyNotRising, start, final => totalEnergy final.bodies ≤ totalEnergy start.bodies
  | .massConserved, start, final => totalMass final.bodies = totalMass start.bodies
  | .populationConserved, start, final => final.bodies.length = start.bodies.length

instance (c : Claim) (s f : World) : Decidable (c.holds s f) := by
  cases c <;> unfold Claim.holds <;> infer_instance

/-- Which events a result talks about. -/
inductive EventScope where
  /-- Only events a protected universe permits. -/
  | allowed
  /-- Every event that can be written down. -/
  | any
  /-- No events at all: time passes and the laws run. -/
  | timeOnly
  deriving DecidableEq, Repr

/-! ## Checking a trace -/

/-- A claimed run of a universe. -/
abbrev WorldTrace := Trace World EnvironmentEvent

/-- Every event in the trace is in scope. -/
def InScope : EventScope → World → List EnvironmentEvent → Prop
  | .allowed, w, es => AllowedTrace step Allowed w es
  | .any, _, _ => True
  | .timeOnly, _, es => ∀ e ∈ es, e = .idle

instance (s : EventScope) (w : World) (es : List EnvironmentEvent) :
    Decidable (InScope s w es) := by
  cases s <;> unfold InScope <;> infer_instance

/-- Replay a trace through `step` and check that it breaks the claim. Only this check turns a trace
into evidence. -/
def checkTrace (scope : EventScope) (claim : Claim) (t : WorldTrace) : Bool :=
  decide (t.states = statesOf step t.initial t.events) &&
  decide (InScope scope t.initial t.events) &&
  decide (¬ claim.holds t.initial t.final)

/-- **A checked counterexample is real.** The events are in scope, and running them through the real
transition function breaks the claim. -/
theorem checkTrace_sound {scope : EventScope} {claim : Claim} {t : WorldTrace}
    (h : checkTrace scope claim t = true) :
    InScope scope t.initial t.events ∧ ¬ claim.holds t.initial (run t.initial t.events) := by
  simp only [checkTrace, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hreplay, hscope⟩, hbad⟩ := h
  exact ⟨hscope, Trace.violates (P := claim.holds t.initial) hreplay hbad⟩

/-! ## Searching for a counterexample -/

/-- Limits on the search. -/
structure SearchLimits where
  /-- How many events to try in a row. -/
  depth : Nat := 3
  /-- The most states to look at. -/
  budget : Nat := 2000
  /-- How many steps of "nothing happens" to try. -/
  idleSteps : Nat := 64
  deriving Repr

/-- A big push along each axis, relative to this world's limits. -/
def bigVectors (w : World) : List Vec3 :=
  let m := max w.laws.maxSpeed 1
  [⟨m, 0, 0⟩, ⟨0, m, 0⟩, ⟨0, 0, m⟩, ⟨-m, -m, -m⟩]

/-- A valid new body in this world, at the centre, with a new id. -/
def probeBody (w : World) : Body :=
  let b := w.bounds
  { id := w.nextId
    shape := (w.bodies.head?.map (·.shape)).getD (.sphere 0)
    position := ⟨(b.minX + b.maxX) / 2, (b.minY + b.maxY) / 2, (b.minZ + b.maxZ) / 2⟩
    velocity := Vec3.zero
    mass := 1
    charge := 0 }

/-- Events within the rules that tend to expose problems. -/
def gentleCandidates (w : World) : List EnvironmentEvent :=
  let m := max w.laws.maxAcceleration 1
  [ .idle, .reverseGravity,
    .changeGravity ⟨m, 0, 0⟩, .changeGravity ⟨0, -m, 0⟩, .changeGravity ⟨0, 0, m⟩,
    .spawnBody (probeBody w), .reverseTime, .changeRestitution 0 ] ++
  (w.bodies.head?.map fun b => (bigVectors w).map (.applyImpulse b.id)).getD []

/-- Events that break the rules on purpose. -/
def wildCandidates (w : World) : List EnvironmentEvent :=
  let m := max w.laws.maxSpeed 1
  [ .changeMaxSpeed (-1), .changeRestitution 5, .setMassRate (-1), .setMassRate 0,
    .changeBounds { w.bounds with maxX := w.bounds.minX - 1 },
    .spawnBody { probeBody w with mass := 0 },
    .spawnBody { probeBody w with id := (w.bodies.head?.map (·.id)).getD 0 },
    .addPortal ⟨w.bounds, none, .scale 1000⟩,
    .addRule (.body .all (.scaleVelocity 1000)),
    .addRule (.body .all (.translate ⟨m * 1000, 0, 0⟩)),
    .addRule (.body .all (.scaleMass 0)) ]

/-- The events to try next, for this scope. -/
def candidateEvents (scope : EventScope) (w : World) : List EnvironmentEvent :=
  match scope with
  | .allowed => (gentleCandidates w).filter fun e => decide (Allowed w e)
  | .any => gentleCandidates w ++ wildCandidates w
  | .timeOnly => [.idle]

/-- One layer of the search: the first run that breaks the claim, and the next frontier. Events are
stored most recent first. -/
def searchLayer (scope : EventScope) (claim : Claim) (start : World)
    (frontier : List (World × List EnvironmentEvent)) :
    Option (List EnvironmentEvent) × List (World × List EnvironmentEvent) :=
  frontier.foldl
    (fun acc node =>
      match acc.1 with
      | some _ => acc
      | none =>
        let next := (candidateEvents scope node.1).map fun e => (step node.1 e, e :: node.2)
        match next.find? (fun n => decide (¬ claim.holds start n.1)) with
        | some hit => (some hit.2, [])
        | none => (none, acc.2 ++ next))
    (none, [])

/-- Search breadth-first up to the limits. -/
def searchDepth (scope : EventScope) (claim : Claim) (start : World) (budget : Nat) :
    Nat → List (World × List EnvironmentEvent) → Option (List EnvironmentEvent)
  | 0, _ => none
  | d + 1, frontier =>
    let layer := searchLayer scope claim start (frontier.take budget)
    match layer.1 with
    | some es => some es
    | none => searchDepth scope claim start budget d layer.2

/-- Turn events into a full trace by replaying them. -/
def traceOf (w : World) (events : List EnvironmentEvent) : WorldTrace :=
  ⟨w, events, statesOf step w events⟩

/-- Find a checked counterexample within the limits. Finding none proves nothing. -/
def searchCounterexample (limits : SearchLimits) (scope : EventScope) (claim : Claim)
    (w : World) : Option WorldTrace :=
  let idle := List.replicate limits.idleSteps EnvironmentEvent.idle
  let found : Option (List EnvironmentEvent) :=
    if ¬ claim.holds w w then some []
    else match searchDepth scope claim w limits.budget limits.depth [(w, [])] with
      | some es => some es.reverse
      | none =>
        (List.range limits.idleSteps).findSome? fun n =>
          let es := idle.take (n + 1)
          if ¬ claim.holds w (run w es) then some es else none
  match found with
  | some es =>
    let t := traceOf w es
    if checkTrace scope claim t then some t else none
  | none => none

/-- **Everything the search returns has passed the checker.** -/
theorem searchCounterexample_sound {limits : SearchLimits} {scope : EventScope} {claim : Claim}
    {w : World} {t : WorldTrace} (h : searchCounterexample limits scope claim w = some t) :
    checkTrace scope claim t = true := by
  unfold searchCounterexample at h
  dsimp only at h
  split at h
  · split at h
    next hc =>
      simp only [Option.some.injEq] at h
      exact h ▸ hc
    next => simp at h
  · simp at h

/-! ## Verdicts -/

/-- The possible results of checking anything in PARADOX. -/
inductive Status where
  /-- Lean has checked a theorem that establishes the claim, under the stated assumptions. -/
  | proven
  /-- A concrete run, checked against `step`, breaks the claim. -/
  | counterexample
  /-- Neither the claim nor its failure has been established. -/
  | unknown
  /-- Some required behaviour is missing, so the claim cannot be judged. -/
  | underspecified
  /-- The requirements cannot all be met by any universe. -/
  | inconsistent
  deriving DecidableEq, Repr

/-- The result of checking one claim. -/
structure Verdict where
  claim : Claim
  status : Status
  /-- The Lean theorem behind a `proven` status. -/
  theoremId : Option String
  /-- What the result depends on. -/
  assumptions : List String
  /-- What the status is about. -/
  scope : Option EventScope
  /-- A plain-language explanation. -/
  explanation : String
  /-- A checked run breaking the claim, for a `counterexample` status. -/
  counterexample : Option WorldTrace
  deriving Repr

/-- The rules in the world that the checker could not clear for this guarantee. -/
def uncheckedRules (p : Property) (w : World) : List Rule :=
  w.rules.filter fun r => !(r.envSafe && r.keeps p)

/-- A short name for a guarantee. -/
def Property.name : Property → String
  | .positiveMass => "positive mass"
  | .boundedPosition => "every object stays inside the world"
  | .boundedVelocity => "every velocity is within the speed limit"
  | .safeEnvironment => "the environment stays safe"
  | .uniqueIds => "object ids stay unique"

/-- What a `proven` result for a guarantee depends on. -/
def provenAssumptions (p : Property) : List String :=
  [ s!"The universe starts with \"{p.name}\" true.",
    "The environment starts safe: limits are positive and every object fits in the world.",
    "Every rule in the universe has passed the rule checker for this guarantee.",
    "Only permitted events happen. The theorem says nothing about other events." ]

/-- The verdict for a built-in guarantee. -/
def verifyProperty (limits : SearchLimits) (p : Property) (w : World) : Verdict :=
  if Inv p w then
    { claim := .property p
      status := .proven
      theoremId := some (``run_inv).toString
      assumptions := provenAssumptions p
      scope := some .allowed
      explanation := s!"\"{p.name}\" holds after any finite list of permitted events, \
        for every force law and every other permitted change."
      counterexample := none }
  else
    match searchCounterexample limits .allowed (.property p) w with
    | some t =>
      { claim := .property p
        status := .counterexample
        theoremId := some (``checkTrace_sound).toString
        assumptions := ["Only permitted events are used in this run."]
        scope := some .allowed
        explanation := s!"This run of {t.events.length} permitted events breaks \"{p.name}\"."
        counterexample := some t }
    | none =>
      { claim := .property p
        status := .unknown
        theoremId := none
        assumptions := [s!"The search tried at most {limits.depth} permitted events in a row."]
        scope := none
        explanation := s!"\"{p.name}\" could not be proved, and the search found no run of \
          permitted events that breaks it. This does not mean it is true or false."
        counterexample := none }

/-- **A proven verdict is correct.** If the verdict for a guarantee is `proven`, the guarantee holds
after every finite list of permitted events. -/
theorem verifyProperty_proven {limits : SearchLimits} {p : Property} {w : World}
    (h : (verifyProperty limits p w).status = .proven) (events : List EnvironmentEvent)
    (htrace : AllowedTrace step Allowed w events) : p.holds (run w events) := by
  unfold verifyProperty at h
  split at h
  next hinv => exact (run_inv p w events hinv htrace).2.1
  next =>
    split at h <;> simp at h

/-- **A reported counterexample is correct.** Any trace in a verdict has passed the checker, using
only permitted events. -/
theorem verifyProperty_counterexample {limits : SearchLimits} {p : Property} {w : World}
    {t : WorldTrace} (h : (verifyProperty limits p w).counterexample = some t) :
    checkTrace .allowed (.property p) t = true := by
  unfold verifyProperty at h
  split at h
  · simp at h
  · split at h
    next t' ht' =>
      simp only [Option.some.injEq] at h
      exact h ▸ searchCounterexample_sound ht'
    next => simp at h

/-- **Proven and counterexample cannot both be true.** No universe has a proof of a guarantee and a
checked counterexample using permitted events. -/
theorem proven_excludes_counterexample {limits : SearchLimits} {p : Property} {w : World}
    (h : (verifyProperty limits p w).status = .proven) {t : WorldTrace} (ht : t.initial = w)
    (hc : checkTrace .allowed (.property p) t = true) : False := by
  obtain ⟨hscope, hbad⟩ := checkTrace_sound hc
  rw [ht] at hscope hbad
  exact hbad (verifyProperty_proven h t.events hscope)

/-- A constraint that the built-in guarantees already cover. -/
def Constraint.coveredBy (c : Constraint) : Option Property :=
  if c = .body .mass .gt 0 then some .positiveMass else none

theorem Constraint.coveredBy_sound {c : Constraint} {p : Property} (h : c.coveredBy = some p)
    (w : World) (hp : p.holds w) : c.holds w := by
  unfold Constraint.coveredBy at h
  split at h
  next hc =>
    simp only [Option.some.injEq] at h
    subst h hc
    exact hp
  next => simp at h

/-- The verdict for a claim that is not a built-in guarantee: a covering theorem, a checked
counterexample, or unknown. -/
def verifyClaim (limits : SearchLimits) (claim : Claim) (w : World) : Verdict :=
  let fromCover : Option Verdict :=
    match claim with
    | .property p => some (verifyProperty limits p w)
    | .constraint c =>
      match c.coveredBy with
      | some p =>
        if Inv p w then some { verifyProperty limits p w with claim := .constraint c } else none
      | none => none
    | _ => none
  match fromCover with
  | some v => v
  | none =>
    match searchCounterexample limits .allowed claim w with
    | some t =>
      { claim
        status := .counterexample
        theoremId := some (``checkTrace_sound).toString
        assumptions := ["Only permitted events are used in this run."]
        scope := some .allowed
        explanation := s!"This run of {t.events.length} permitted events breaks the claim."
        counterexample := some t }
    | none =>
      { claim
        status := .unknown
        theoremId := none
        assumptions := [s!"The search tried at most {limits.depth} permitted events in a row."]
        scope := none
        explanation := "This claim could not be proved, and the search found no run of permitted \
          events that breaks it. This does not mean it is true or false."
        counterexample := none }

end Paradox

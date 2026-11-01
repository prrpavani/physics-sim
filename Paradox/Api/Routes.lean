import Paradox.Api.Catalog

/-!
# The API, as a pure function

Every route takes JSON and returns JSON. The HTTP server only moves bytes, so everything here can be
tested without a network. No route makes a decision about the universe on its own: each one calls
the formal functions and reports what they returned.
-/

namespace Paradox

/-! ## Limits on formulas and rules -/

/-- The number of pieces in a formula. -/
def LawExpr.nodes : LawExpr → Nat
  | .add a b | .sub a b | .mul a b | .div a b => a.nodes + b.nodes + 1
  | .neg a | .pow a _ => a.nodes + 1
  | _ => 1

/-- How deeply powers are stacked in a formula. -/
def LawExpr.powerDepth : LawExpr → Nat
  | .add a b | .sub a b | .mul a b | .div a b => max a.powerDepth b.powerDepth
  | .neg a => a.powerDepth
  | .pow a _ => a.powerDepth + 1
  | _ => 0

/-- The formulas in a rule. -/
def Rule.formulas : Rule → List LawExpr
  | .body _ (.setMassFormula f) => [f]
  | .world (.setPairForce f) => [f]
  | .seq a b => a.formulas ++ b.formulas
  | .when _ r => r.formulas
  | _ => []

/-- The number of pieces in a rule. -/
def Rule.nodes : Rule → Nat
  | .seq a b => a.nodes + b.nodes + 1
  | .when _ r => r.nodes + 1
  | _ => 1

end Paradox

namespace Paradox.Api

open Lean (Json)

/-- The contract version. Changing the wire format means changing this. -/
def contractVersion : String := "1.0.0"

/-- The most bodies a request may contain. -/
def maxBodies : Nat := 256
/-- The most steps one request may run. -/
def maxSteps : Nat := 5000
/-- The largest formula or rule a request may contain. -/
def maxNodes : Nat := 256
/-- The deepest powers may be stacked in one formula. -/
def maxPowerDepth : Nat := 2

/-- The formula is small enough to evaluate safely. -/
def formulaOk (e : LawExpr) : Bool :=
  e.nodes ≤ maxNodes && e.powerDepth ≤ maxPowerDepth

/-- The rule is small enough to run safely. -/
def ruleOk (r : Rule) : Bool :=
  r.nodes ≤ maxNodes && r.formulas.all formulaOk

/-- A limit on bodies squared times steps, which is about how much work a run does. -/
def maxRunWork : Nat := 5000000

/-- A limit on bodies squared times states searched. -/
def maxSearchWork : Nat := 2000000

/-- About how many states one unit of search budget visits per level: one per candidate event. -/
def statesPerBudget : Nat := 12

/-- Lower search limits so a large world cannot take too long. A lower limit can only turn a
counterexample into `unknown`, which stays honest. -/
def fitLimits (w : World) (l : SearchLimits) : SearchLimits :=
  let squared := max 1 (w.bodies.length * w.bodies.length)
  let room := maxSearchWork / squared
  { l with
    budget := min l.budget (room / (statesPerBudget * max 1 l.depth))
    idleSteps := min l.idleSteps room }

/-- Reject a world too large to process. -/
def checkWorld (w : World) : Dec Unit := do
  if w.bodies.length > maxBodies then throw s!"at most {maxBodies} bodies are supported"
  unless formulaOk w.laws.pairForce && formulaOk w.laws.drag && formulaOk w.laws.central do
    throw "a formula is too large"
  unless w.rules.all ruleOk do throw "a rule is too large"

/-- Reject an event too large to process. -/
def checkEvent : EnvironmentEvent → Dec Unit
  | .setPairForce f | .setDrag f | .setCentral f =>
    unless formulaOk f do throw "the formula is too large"
  | .addRule r => unless ruleOk r do throw "the rule is too large"
  | _ => pure ()

/-- Read and check the `world` field. -/
def worldField (j : Json) : Dec World := do
  let w ← decWorld (← field j "world")
  checkWorld w
  return w

/-- Read and check an event. -/
def eventOf (j : Json) : Dec EnvironmentEvent := do
  let e ← decEvent j
  checkEvent e
  return e

/-- The search limits of a request, lowered to suit this world. -/
def limitsOf (j : Json) (w : World) : Dec SearchLimits :=
  match optField j "limits" with
  | some l => fitLimits w <$> decLimits l
  | none => pure (fitLimits w {})

/-- Which built-in guarantees are false in this world. -/
def violations (w : World) : List Property :=
  Property.all.filter fun p => !decide (p.holds w)

/-- Which of the user's constraints are false in this world. -/
def brokenConstraints (cs : List Constraint) (w : World) : List Constraint :=
  cs.filter fun c => !decide (c.holds w)

/-! ## Universe creation -/

def routeCreate (j : Json) : Dec Json := do
  let seed ← match optField j "seed" with
    | some s => decNat s
    | none => pure 1
  let name ← match optField j "preset" with
    | some p => decStr p
    | none => pure "normal"
  match presets.find? (·.name == name) with
  | none => throw s!"unknown preset '{name}'"
  | some p =>
    let w := presetWorld p seed
    return Json.mkObj [("world", encWorld w), ("preset", p.name), ("seed", (seed : Nat)),
      ("guaranteed", Json.bool (decide (Guaranteed w)))]

/-! ## Stepping -/

/-- Whether a request is for protected mode. -/
def isProtected (j : Json) : Dec Bool :=
  match optField j "mode" with
  | some (.str "protected") => pure true
  | some (.str "unprotected") => pure false
  | none => pure false
  | _ => throw "mode must be 'protected' or 'unprotected'"

/-- The result of one step. -/
structure StepResult where
  world : World
  decision : Option Decision
  /-- A constraint would have been broken, so the world did not change. -/
  frozen : Bool

/-- One step in the requested mode. -/
def doStep (isProt : Bool) (cs : List Constraint) (w : World) (e : EnvironmentEvent) : StepResult :=
  if isProt then
    let r := protectedStep w e
    if cs.all (fun c => decide (c.holds r.1)) then ⟨r.1, some r.2, false⟩
    else ⟨w, some r.2, true⟩
  else ⟨step w e, none, false⟩

def routeStep (j : Json) : Dec Json := do
  let w ← worldField j
  let e ← eventOf (← field j "event")
  let isProt ← isProtected j
  let cs ← listFieldD decConstraint j "constraints"
  let r := doStep isProt cs w e
  return Json.mkObj [("world", encWorld r.world),
    ("mode", if isProt then "protected" else "unprotected"),
    ("decision", match r.decision with
      | some d => encDecision d
      | none => Json.null),
    ("frozen", Json.bool r.frozen),
    ("violations", encList encProperty (violations r.world)),
    ("brokenConstraints", encList encConstraint (brokenConstraints cs r.world))]

/-- One frame sent to the renderer. -/
def encFrame (w : World) (d : Option Decision) : Json :=
  Json.mkObj [("tick", (w.tick : Nat)), ("bodies", encList encBody w.bodies),
    ("decision", match d with
      | some x => encDecision x
      | none => Json.null),
    ("violations", encList encProperty (violations w))]

def routeRun (j : Json) : Dec Json := do
  let w ← worldField j
  let events ← listFieldD eventOf j "events"
  let isProt ← isProtected j
  let cs ← listFieldD decConstraint j "constraints"
  let steps ← match optField j "steps" with
    | some s => decNat s
    | none => pure events.length
  if steps > maxSteps then throw s!"at most {maxSteps} steps per request"
  if events.length > maxSteps then throw s!"at most {maxSteps} events per request"
  let total := max steps events.length
  if w.bodies.length * w.bodies.length * total > maxRunWork then
    throw "too many bodies for this many steps"
  let every ← match optField j "frameEvery" with
    | some s => decNat s
    | none => pure 1
  let eventAt (i : Nat) : EnvironmentEvent := events.getD i .idle
  let mut current := w
  let mut frames : Array Json := #[]
  for i in [0:total] do
    let r := doStep isProt cs current (eventAt i)
    current := r.world
    if every != 0 && (i + 1) % every == 0 then
      frames := frames.push (encFrame current r.decision)
  return Json.mkObj [("frames", Json.arr frames), ("world", encWorld current),
    ("violations", encList encProperty (violations current))]

/-! ## Rule checks -/

/-- Everything the rule checker says about one rule. -/
def encRuleReport (w : Option World) (r : Rule) : Json :=
  let keeps := Property.all.map fun p => (p, r.keeps p)
  let missing := match w with
    | some world => r.regionNames.filter fun n => !(world.regions.any (·.name == n))
    | none => []
  let status : Status :=
    if !missing.isEmpty then .underspecified
    else if r.certified then .proven
    else .unknown
  Json.mkObj [("rule", encRule r), ("status", encStatus status),
    ("certified", Json.bool r.certified), ("environmentSafe", Json.bool r.envSafe),
    ("keeps", encList (fun p => Json.mkObj [("property", encProperty p.1), ("cleared", Json.bool p.2)]) keeps),
    ("missingRegions", encList Json.str missing),
    ("repair", match r.repair with
      | some fixed => encRule fixed
      | none => Json.null),
    ("theoremId", (``Rule.keeps_sound).toString),
    ("explanation",
      if !missing.isEmpty then "This rule names a region the universe does not have."
      else if r.certified then "This rule keeps every guarantee in every safe universe."
      else "The checker could not clear this rule for every guarantee. It may still be safe. Use \
        find-counterexample to look for a run that breaks it.")]

def routeValidateRules (j : Json) : Dec Json := do
  let rules ← match optField j "rule" with
    | some r => do pure [← decRule r]
    | none => listFieldD decRule j "rules"
  unless rules.all ruleOk do throw "a rule is too large"
  let w ← match optField j "world" with
    | some v => some <$> decWorld v
    | none => pure none
  return Json.mkObj [("rules", encList (encRuleReport w) rules)]

/-! ## The three layers -/

/-- Layer A as JSON. -/
def encRuleLayer (base : World) (cs : List Constraint) : Json :=
  match checkConstraints base cs with
  | .satisfiable w =>
    Json.mkObj [("status", encStatus .proven),
      ("theoremId", (``checkConstraints_satisfiable).toString),
      ("witness", encWorld w),
      ("checked", "Whether one universe with at least one object can meet every constraint."),
      ("assumptions", encList Json.str
        ["Same box and speed limit as this universe.", "At least one object exists.",
         "Every built-in guarantee holds in that universe."]),
      ("explanation", "This example universe meets every constraint.")]
  | .contradiction a b =>
    Json.mkObj [("status", encStatus .inconsistent),
      ("theoremId", (``checkConstraints_contradiction).toString),
      ("conflict", encList encConstraint [a, b]),
      ("checked", "Whether one universe with at least one object can meet every constraint."),
      ("assumptions", encList Json.str
        ["Same box and speed limit as this universe.", "At least one object exists."]),
      ("explanation", "These two requirements cannot both be true of any object. One may be \
        built in, such as positive mass or the speed limit.")]
  | .unknown =>
    Json.mkObj [("status", encStatus .unknown), ("theoremId", Json.null),
      ("checked", "Whether one universe with at least one object can meet every constraint."),
      ("assumptions", encList Json.str []),
      ("explanation", "The check found no example universe and no contradiction. The constraints \
        may or may not be possible together.")]

/-- Layer B as JSON. -/
def encTransitionLayer (w : World) : Json :=
  let r := checkTransitions w
  let underspecified := !r.missingRegions.isEmpty || !r.portalsWithoutExit.isEmpty ||
    !r.undefinedFormulas.isEmpty
  let status : Status :=
    if underspecified then .underspecified
    else if !r.conflicts.isEmpty then .counterexample
    else if !r.unknownFormulas.isEmpty then .unknown
    else .proven
  let explanation :=
    match status with
    | .underspecified => "Some behaviour is missing. The simulation uses a default for it \
        (dividing by zero gives zero; a portal with no exit leaves the object in place)."
    | .counterexample => "Every next state is defined, but some rules give different results \
        depending on their order. The rule list decides the order."
    | .unknown => "No missing behaviour was found, but a formula could not be proved defined."
    | _ => "Every formula has a defined value, every name resolves, and every portal has an exit. \
        Each event gives exactly one next state."
  Json.mkObj [("status", encStatus status),
    ("theoremId", match status with
      | .counterexample => Json.str (``orderStatus_conflict).toString
      | .proven => Json.str (``LawExpr.divisionsSafe_sound).toString
      | _ => Json.null),
    ("checked", "Whether the rules say what happens next, without relying on a default."),
    ("deterministic", Json.bool true),
    ("deterministicTheorem", (``Engine.deterministic_of_function).toString),
    ("missingRegions", encList Json.str r.missingRegions),
    ("portalsWithoutExit", encList encPortal r.portalsWithoutExit),
    ("undefinedFormulas", encList (fun p => Json.str p.1) r.undefinedFormulas),
    ("unknownFormulas", encList Json.str r.unknownFormulas),
    ("ruleConflicts", encList (fun p => Json.arr #[encRule p.1, encRule p.2]) r.conflicts),
    ("explanation", explanation)]

def routeCheckConsistency (j : Json) : Dec Json := do
  let w ← worldField j
  let cs ← listFieldD decConstraint j "constraints"
  let limits ← limitsOf j w
  let props ← listFieldD decProperty j "properties" Property.all
  let claims := props.map Claim.property ++ cs.map Claim.constraint
  return Json.mkObj [("ruleConsistency", encRuleLayer w cs),
    ("transitionConsistency", encTransitionLayer w),
    ("evolutionConsistency",
      Json.mkObj [("verdicts", encList encVerdict (claims.map fun c => verifyClaim limits c w))])]

/-! ## Verification -/

def routeVerify (j : Json) : Dec Json := do
  let w ← worldField j
  let limits ← limitsOf j w
  let claims ← match optField j "claim", optField j "property" with
    | some c, _ => do pure [← decClaim c]
    | _, some p => do pure [Claim.property (← decProperty p)]
    | _, _ =>
      let fromProps ← listFieldD decProperty j "properties" []
      let fromClaims ← listFieldD decClaim j "claims" []
      pure (fromProps.map Claim.property ++ fromClaims)
  let chosen := if claims.isEmpty then Property.all.map Claim.property else claims
  return Json.mkObj [("verdicts", encList encVerdict (chosen.map fun c => verifyClaim limits c w))]

def routeCounterexample (j : Json) : Dec Json := do
  let w ← worldField j
  let limits ← limitsOf j w
  let claim ← match optField j "claim", optField j "property" with
    | some c, _ => decClaim c
    | _, some p => Claim.property <$> decProperty p
    | _, _ => throw "give a 'claim' or a 'property'"
  let scope ← match optField j "scope" with
    | some s => decScope s
    | none => pure .any
  match searchCounterexample limits scope claim w with
  | some t =>
    return Json.mkObj [("status", encStatus .counterexample), ("checked", Json.bool true),
      ("theoremId", (``checkTrace_sound).toString), ("scope", encScope scope),
      ("counterexample", encTrace t)]
  | none =>
    return Json.mkObj [("status", encStatus .unknown), ("checked", Json.bool false),
      ("theoremId", Json.null), ("scope", encScope scope), ("counterexample", Json.null),
      ("explanation", "No counterexample was found within the limits. This does not mean the \
        claim is true.")]

def routeCheckTrace (j : Json) : Dec Json := do
  let t ← decTrace (← field j "trace")
  checkWorld t.initial
  let claim ← decClaim (← field j "claim")
  let scope ← match optField j "scope" with
    | some s => decScope s
    | none => pure .any
  return Json.mkObj [("valid", Json.bool (checkTrace scope claim t)),
    ("replays", Json.bool (decide (t.states = Engine.statesOf step t.initial t.events))),
    ("inScope", Json.bool (decide (InScope scope t.initial t.events))),
    ("breaksClaim", Json.bool (decide (¬ claim.holds t.initial t.final))),
    ("theoremId", (``checkTrace_sound).toString)]

/-! ## Events -/

def routeCheckEvent (j : Json) : Dec Json := do
  let w ← worldField j
  let e ← eventOf (← field j "event")
  return Json.mkObj [("allowed", Json.bool (decide (Allowed w e))),
    ("decision", encDecision (decideEvent w e))]

def routeRandomEvents (j : Json) : Dec Json := do
  let seed ← decNat (← field j "seed")
  let count ← decNat (← field j "count")
  if count > maxSteps then throw s!"at most {maxSteps} events per request"
  let kind ← match optField j "kind" with
    | some k => decStr k
    | none => pure "safe"
  match kind with
  | "safe" =>
    return Json.mkObj [("events", encList encEvent (safeEvents seed count)), ("seed", (seed : Nat)),
      ("kind", "safe"), ("alwaysAllowed", Json.bool true),
      ("theoremId", (``safeEvents_allowed).toString)]
  | "wild" =>
    return Json.mkObj [("events", encList encEvent (wildEvents seed count)), ("seed", (seed : Nat)),
      ("kind", "wild"), ("alwaysAllowed", Json.bool false), ("theoremId", Json.null)]
  | _ => throw "kind must be 'safe' or 'wild'"

/-! ## Conservation audit -/

def routeAuditLaws (j : Json) : Dec Json := do
  let w ← worldField j
  let limits ← limitsOf j w
  let interaction := auditInteractionMomentum w
  let fullStep (d : Vec3) := searchedVerdict limits (.momentumConserved d) .timeOnly "Momentum conservation" w
  return Json.mkObj [
    ("mass", encVerdict (auditMass limits w)),
    ("energy", encVerdict (auditEnergy limits w)),
    ("population", encVerdict
      (searchedVerdict limits .populationConserved .timeOnly "Population staying constant" w)),
    ("momentumBetweenBodies", Json.mkObj [
      ("status", encStatus interaction.1),
      ("theoremId", match interaction.1 with
        | .proven => Json.str interaction.2.1
        | _ => Json.null),
      ("basis", interaction.2.1),
      ("assumptions", encList Json.str interaction.2.2)]),
    ("momentumFullStep", encList (fun d => encVerdict (fullStep d))
      [⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩])]

/-! ## Router -/

/-- A response: the HTTP status and the JSON body. -/
structure Reply where
  code : Nat
  body : Json

/-- A successful result or a client error, as a reply. -/
def replyOf (r : Dec Json) : Reply :=
  match r with
  | .ok j => ⟨200, j⟩
  | .error e => ⟨400, Json.mkObj [("error", e)]⟩

/-- What each route accepts, for discovery. -/
def routeList : List (String × String × String) :=
  [ ("GET", "/api/health", "Status and contract version."),
    ("GET", "/api/theorems", "Every theorem, in plain language, with assumptions."),
    ("GET", "/api/presets", "The ready-made universes."),
    ("POST", "/api/universe/create", "Make a universe from a preset and seed."),
    ("POST", "/api/universe/step", "One transition, protected or unprotected."),
    ("POST", "/api/universe/run", "Many transitions, returning frames."),
    ("POST", "/api/universe/validate-rules", "What the rule checker says about rules."),
    ("POST", "/api/universe/check-consistency", "All three consistency layers."),
    ("POST", "/api/universe/verify-property", "Verdicts for guarantees and claims."),
    ("POST", "/api/universe/find-counterexample", "Search for a checked counterexample."),
    ("POST", "/api/universe/check-trace", "Check any trace against the formal model."),
    ("POST", "/api/universe/check-event", "What protected mode would do with an event."),
    ("POST", "/api/universe/random-events", "A reproducible list of random events."),
    ("POST", "/api/universe/audit-laws", "Which conservation laws hold under these laws.") ]

/-- Handle one request. -/
def handle (method path : String) (body : String) : Reply :=
  let withJson (f : Json → Dec Json) : Reply :=
    match Json.parse (if body.isEmpty then "{}" else body) with
    | .ok j => replyOf (f j)
    | .error e => ⟨400, Json.mkObj [("error", s!"invalid JSON: {e}")]⟩
  match method, path with
  | "GET", "/api/health" =>
    ⟨200, Json.mkObj [("status", "ok"), ("contractVersion", contractVersion),
      ("engine", "Lean 4 formal model"),
      ("routes", encList (fun r => Json.mkObj
        [("method", r.1), ("path", r.2.1), ("description", r.2.2)]) routeList)]⟩
  | "GET", "/api/theorems" => ⟨200, Json.mkObj [("theorems", encList encTheorem theorems)]⟩
  | "GET", "/api/presets" => ⟨200, Json.mkObj [("presets", encList encPreset presets)]⟩
  | "POST", "/api/universe/create" => withJson routeCreate
  | "POST", "/api/universe/step" => withJson routeStep
  | "POST", "/api/universe/run" => withJson routeRun
  | "POST", "/api/universe/validate-rules" => withJson routeValidateRules
  | "POST", "/api/universe/check-consistency" => withJson routeCheckConsistency
  | "POST", "/api/universe/verify-property" => withJson routeVerify
  | "POST", "/api/universe/find-counterexample" => withJson routeCounterexample
  | "POST", "/api/universe/check-trace" => withJson routeCheckTrace
  | "POST", "/api/universe/check-event" => withJson routeCheckEvent
  | "POST", "/api/universe/random-events" => withJson routeRandomEvents
  | "POST", "/api/universe/audit-laws" => withJson routeAuditLaws
  | _, _ => ⟨404, Json.mkObj [("error", s!"no route for {method} {path}")]⟩

end Paradox.Api

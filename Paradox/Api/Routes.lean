import Paradox.Api.Json

/-!
# The API, as pure functions

Each route calls the formal functions and reports what they returned. No route decides anything about
a universe on its own.
-/

namespace Paradox.Api

open Lean (Json)

/-- The most steps one request may run. -/
def maxSteps : Nat := 2000

/-- The most objects a request may contain. -/
def maxBodies : Nat := 64

/-- Everything the app shows about a promise that is fixed, not computed. -/
structure PromiseInfo where
  promise : Promise
  key : String
  title : String
  /-- What the promise says. -/
  meaning : String
  /-- The result worth noticing. -/
  insight : String
  /-- The theorems to show, in order. -/
  theorems : List Lean.Name
  /-- What is proved, and what it does not say. -/
  limits : String

/-- The four promises, as the app presents them. -/
def promiseInfos : List PromiseInfo :=
  [ ⟨.staysInside, "staysInside", "Objects stay inside",
      "Every object is fully inside the world.",
      "No setting of these laws can break this one.",
      [``stays_inside, ``stays_inside_forever],
      "Each step ends by keeping objects inside, so this shows that always works. See below for proof that it only acts when it must."⟩,
    ⟨.speedLimit, "speedLimit", "Speed limit",
      "Every velocity component stays within the limit.",
      "Multiplying velocity by 100 breaks this. Adding the limiter makes the same law provably safe.",
      [``speedLimit_holds, ``speedLimit_forever, ``locked_run_safe],
      "It holds after each step from the current laws on. It does not cover laws that fail the conditions, which may or may not break it."⟩,
    ⟨.momentum, "momentum", "Momentum between objects",
      "The pull between objects does not change their total momentum.",
      "True for any pull strength and any masses, and false the moment the third law is off.",
      [``momentum_holds, ``momentum_forever],
      "It covers objects acting on each other. Gravity and walls do change total momentum."⟩,
    ⟨.energy, "energy", "Energy never rises",
      "Total kinetic energy can only stay level or fall.",
      "You cannot have this promise and gravity together: falling objects gain energy.",
      [``energy_never_rises, ``energy_forever, ``wall_never_speeds_up],
      "This is about kinetic energy, which is all the model has. It is not conservation: walls and rounding can remove energy."⟩ ]

/-- Which conditions a promise depends on, each with whether it holds now. -/
def conditionsOf (p : Promise) (l : Laws) : List (String × Bool) :=
  let bounce := decide (l.restitution ≤ 1)
  let multiply := decide (|l.multiplier| ≤ 1)
  match p with
  | .staysInside => []
  | .speedLimit =>
    [("The limiter is on", l.limiter), ("Or: bounciness is at most 1", bounce),
     ("And the multiplier's size is at most 1", multiply)]
  | .momentum => [("Newton's third law is on", l.thirdLaw), ("Or: there is no pull", decide (l.pull = 0))]
  | .energy =>
    [("No gravity", decide (l.gravity = 0)), ("No pull", decide (l.pull = 0)),
     ("Bounciness is at most 1", bounce), ("The multiplier's size is at most 1", multiply)]

def encStatus : Status → Json
  | .proven => "proven"
  | .counterexample => "counterexample"
  | .unproven => "unproven"

def encTrace (t : Trace) : Json :=
  Json.mkObj [("start", encWorld t.start), ("states", Json.arr (t.states.map encWorld).toArray)]

/-- One card. -/
def encCard (info : PromiseInfo) (w : World) : Json :=
  let v := verdict info.promise w
  let fromProbe := match v.2 with
    | some t => decide (t.start ≠ w)
    | none => false
  let statusText := match v.1 with
    | .proven => "Lean proved this holds at every future step, under these laws."
    | .counterexample =>
      if fromProbe then "Lean checked a run from a small test universe under these laws. It breaks this promise."
      else "Lean checked a run of this universe that breaks this promise."
    | .unproven => "Not proved, and the search found no run that breaks it. This does not mean it is true or false."
  Json.mkObj [("key", info.key), ("title", info.title), ("meaning", info.meaning),
    ("insight", info.insight), ("limits", info.limits), ("status", encStatus v.1),
    ("statusText", statusText),
    ("conditions", Json.arr ((conditionsOf info.promise w.laws).map fun c =>
      Json.mkObj [("text", c.1), ("met", Json.bool c.2)]).toArray),
    ("theorems", Json.arr (info.theorems.map fun n => Json.str n.toString).toArray),
    ("trace", match v.2 with
      | some t => encTrace t
      | none => Json.null),
    ("fromProbe", Json.bool fromProbe)]

/-- Which promises this exact state breaks. -/
def encBroken (w : World) : Json :=
  Json.mkObj [("staysInside", Json.bool (!decide (StaysInside w))),
    ("speedLimit", Json.bool (!decide (WithinSpeedLimit w)))]

def checkWorld (w : World) : Dec Unit := do
  if w.bodies.length > maxBodies then throw s!"at most {maxBodies} objects are supported"
  if !decide (WellFormed w) then throw "this universe is not valid: check its laws and objects"

def routeCreate : Json :=
  Json.mkObj [("world", encWorld startWorld)]

def encDecision : Decision → String
  | .accepted _ => "accepted"
  | .repaired _ => "repaired"
  | .refused => "refused"

/-- Run some steps. New laws, if any, apply first, through the lock if it is on. -/
def routeRun (j : Json) : Dec Json := do
  let w0 ← decWorld (← field j "world")
  if w0.bodies.length > maxBodies then throw s!"at most {maxBodies} objects are supported"
  let steps ← natField j "steps"
  if steps > maxSteps then throw s!"at most {maxSteps} steps per request"
  let locked ← boolField j "locked"
  let newLaws ← match j.getObjVal? "laws" with
    | .ok v => if v.isNull then pure none else some <$> decLaws v
    | .error _ => pure none
  let (w1, decision) : World × Option String :=
    match newLaws with
    | none => (w0, none)
    | some l =>
      if locked then (lockedSetLaws w0 l, some (encDecision (decideLaws l)))
      else ({ w0 with laws := l }, some "accepted")
  let mut current := w1
  let mut frames : Array Json := #[]
  for _ in [0:steps] do
    current := tick current
    frames := frames.push (Json.mkObj [("tick", (current.tick : Nat)),
      ("bodies", Json.arr (current.bodies.map encBody).toArray), ("broken", encBroken current)])
  return Json.mkObj [("frames", Json.arr frames), ("world", encWorld current),
    ("laws", encLaws w1.laws),
    ("decision", match decision with
      | some d => Json.str d
      | none => Json.null)]

def routeVerdicts (j : Json) : Dec Json := do
  let w ← decWorld (← field j "world")
  checkWorld w
  return Json.mkObj [("cards", Json.arr (promiseInfos.map (encCard · w)).toArray)]

/-- The block of source text that declares this theorem. Blocks are separated by blank lines. -/
def proofBlock (source : String) (name : String) : Option String :=
  let short := (name.splitOn ".").getLast?.getD name
  (source.splitOn "\n\n").find? fun block =>
    (block.splitOn s!"theorem {short} ").length > 1

/-- The text of every theorem the app shows, read from the source that Lean compiled. -/
def proofsJson (sources : List String) : Json :=
  let names := (promiseInfos.flatMap (·.theorems)).map (·.toString)
  let extra := [``checkTrace_sound, ``verdict_proven_sound, ``free_motion, ``wall_bounce].map (·.toString)
  Json.mkObj [("proofs", Json.mkObj ((names ++ extra).map fun n =>
      (n, match sources.findSome? (proofBlock · n) with
        | some text => Json.str text
        | none => Json.null))),
    ("general", Json.arr (extra.map Json.str).toArray),
    ("axioms", Json.arr #["propext", "Classical.choice", "Quot.sound"])]

/-- A response: the HTTP status and the JSON body. -/
structure Reply where
  code : Nat
  body : Json

/-- Handle one request, given the text of the proof files. -/
def handle (method path body : String) (sources : List String) : Reply :=
  let withJson (f : Json → Dec Json) : Reply :=
    match Json.parse body >>= f with
    | .ok j => ⟨200, j⟩
    | .error e => ⟨400, Json.mkObj [("error", e)]⟩
  match method, path with
  | "POST", "/api/create" => ⟨200, routeCreate⟩
  | "POST", "/api/run" => withJson routeRun
  | "POST", "/api/verdicts" => withJson routeVerdicts
  | "GET", "/api/proofs" => ⟨200, proofsJson sources⟩
  | _, _ => ⟨404, Json.mkObj [("error", s!"no route for {method} {path}")]⟩

end Paradox.Api

import Lean.Data.Json
import Paradox.Verification.Preservation

/-!
# The browser interface

Turns requests from the browser into calls to `step`, and worlds back into JSON. Nothing here
changes how the world moves: every frame the browser draws is `step w e` for some event `e`.
The message format is in `docs/FRONTEND_CONTRACT.md`.

This file also tracks, frame by frame, whether each guarantee is **proven** (a theorem in
`Preservation.lean` covers the run so far), **violated** (a computed state breaks it) or
**unknown** (an event outside the theorem's assumptions ran, but no state has broken it yet).
-/

namespace Paradox.Api

open Lean (Json ToJson toJson)

/-! ## Deciding the invariants on one concrete world -/

instance (b : Bounds) (p : Vec3) : Decidable (b.Contains p) := by
  unfold Bounds.Contains; infer_instance
instance (b : Bounds) : Decidable b.Valid := by unfold Bounds.Valid; infer_instance
instance (a : Vec3) (m : ℚ) : Decidable (a.WithinAbs m) := by unfold Vec3.WithinAbs; infer_instance
instance (w : World) : Decidable (PositiveMass w) := by unfold PositiveMass; infer_instance
instance (w : World) : Decidable (BoundedPosition w) := by unfold BoundedPosition; infer_instance
instance (w : World) : Decidable (BoundedVelocity w) := by unfold BoundedVelocity; infer_instance
instance (w : World) : Decidable (SafeEnvironment w) := by unfold SafeEnvironment; infer_instance
instance (l : PhysicsLaws) (bs : Bounds) (b : Body) : Decidable (WallNeverSpeedsUp l bs b) := by
  unfold WallNeverSpeedsUp; dsimp only; infer_instance

/-! ## Exact numbers as strings: `"-981/100"` or `"20"` -/

def ratString (q : ℚ) : String :=
  if q.den = 1 then toString q.num else s!"{q.num}/{q.den}"

def parseRat (s : String) : Option ℚ :=
  match s.splitOn "/" with
  | [n] => n.toInt?.map fun i => (i : ℚ)
  | [n, d] => do
    let n ← n.toInt?
    let d ← d.toNat?
    if d = 0 then none else some ((n : ℚ) / (d : ℚ))
  | _ => none

#guard parseRat "-981/100" == some (-981 / 100)
#guard parseRat "20" == some 20
#guard parseRat "1/0" == none
#guard ratString (-981 / 100) == "-981/100"
#guard ratString 3 == "3"

abbrev Parse := Except String

def ratOf (j : Json) : Parse ℚ := do
  let s ← j.getStr?
  match parseRat s with
  | some q => pure q
  | none => throw s!"not a number: {s}"

def rat (j : Json) (key : String) : Parse ℚ := do ratOf (← j.getObjVal? key)

def vecOf (j : Json) : Parse Vec3 := do
  match (← j.getArr?).toList with
  | [x, y, z] => return ⟨← ratOf x, ← ratOf y, ← ratOf z⟩
  | _ => throw "a vector needs three numbers"

def vec (j : Json) (key : String) : Parse Vec3 := do vecOf (← j.getObjVal? key)

def ratJ (q : ℚ) : Json := Json.str (ratString q)
def vecJ (v : Vec3) : Json := Json.arr #[ratJ v.x, ratJ v.y, ratJ v.z]

/-! ## Worlds -/

/-- A world as the browser sent it, with the Lean `World` read out of it. Each body keeps its
JSON, so fields the Lean model does not use (id, material, temperature) pass through unchanged. -/
structure State where
  world : World
  tick : Nat
  json : Json
  bodies : Array Json

def bodyOf (j : Json) : Parse Body :=
  return { position := ← vec j "position", velocity := ← vec j "velocity", mass := ← rat j "mass" }

def stateOf (j : Json) : Parse State := do
  let bj ← j.getObjVal? "bounds"
  let lo ← vec bj "min"
  let hi ← vec bj "max"
  let lj ← j.getObjVal? "laws"
  let laws : PhysicsLaws :=
    { gravity := ← vec lj "gravity", maxSpeed := ← rat lj "maxSpeed",
      maxAcceleration := ← rat lj "maxAcceleration", timeStep := ← rat lj "timeStep",
      restitution := ← rat lj "restitution" }
  let bodies ← j.getObjValAs? (Array Json) "bodies"
  let bs ← bodies.toList.mapM bodyOf
  return {
    world := { bodies := bs, bounds := ⟨lo.x, hi.x, lo.y, hi.y, lo.z, hi.z⟩, laws }
    tick := (j.getObjValAs? Nat "tick").toOption.getD 0
    json := j, bodies }

/-- A body's JSON with the Lean values written in. -/
def bodyJson (b : Body) (j : Json) : Json :=
  j.setObjVal! "position" (vecJ b.position)
   |>.setObjVal! "velocity" (vecJ b.velocity)
   |>.setObjVal! "mass" (ratJ b.mass)

/-- The bodies' JSON, brought up to date with the Lean world. -/
def State.bodiesJson (s : State) : Array Json :=
  ((s.world.bodies.zip s.bodies.toList).map fun (b, j) => bodyJson b j).toArray

def State.encode (s : State) : Json :=
  let l := s.world.laws
  let laws := (s.json.getObjValD "laws")
    |>.setObjVal! "gravity" (vecJ l.gravity)
    |>.setObjVal! "maxSpeed" (ratJ l.maxSpeed)
    |>.setObjVal! "maxAcceleration" (ratJ l.maxAcceleration)
    |>.setObjVal! "timeStep" (ratJ l.timeStep)
    |>.setObjVal! "restitution" (ratJ l.restitution)
  s.json.setObjVal! "tick" (toJson s.tick)
   |>.setObjVal! "laws" laws
   |>.setObjVal! "bodies" (Json.arr s.bodiesJson)

/-- One event, through the real transition function. -/
def State.step (s : State) (e : EnvironmentEvent) : State :=
  { s with world := Paradox.step s.world e, tick := s.tick + 1, bodies := s.bodiesJson }

/-! ## Events and edits -/

/-- What a browser event becomes. Environmental events go through `step`. Edits change the world
directly, between steps; they are not covered by the preservation theorems, so a protected
universe accepts an edit only if the new world satisfies every selected guarantee. -/
inductive Action where
  | env (e : EnvironmentEvent)
  | spawn (body : Json)
  | remove (id : Nat)
  | impulse (id : Nat) (dv : Vec3)
  | setBody (id : Nat) (position velocity : Option Vec3)
  | unsupported (reason : String)

def actionOf (j : Json) : Parse Action := do
  match ← j.getObjValAs? String "type" with
  | "idle" => return .env .idle
  | "setGravity" => return .env (.changeGravity (← vec j "value"))
  | "reverseGravity" => return .env .reverseGravity
  | "disableGravity" => return .env .disableGravity
  | "setLaw" =>
    match ← j.getObjValAs? String "law" with
    | "maxSpeed" => return .env (.changeMaxSpeed (← rat j "value"))
    | "maxAcceleration" => return .env (.changeMaxAcceleration (← rat j "value"))
    | "restitution" => return .env (.changeRestitution (← rat j "value"))
    | law => return .unsupported s!"The Lean model has no rule for '{law}' yet, so it can't run this."
  | "spawnBody" => return .spawn (← j.getObjVal? "body")
  | "removeBody" => return .remove (← j.getObjValAs? Nat "id")
  | "applyImpulse" => return .impulse (← j.getObjValAs? Nat "id") (← vec j "value")
  | "setBody" =>
    let position := (vec j "position").toOption
    let velocity := (vec j "velocity").toOption
    return .setBody (← j.getObjValAs? Nat "id") position velocity
  | other => throw s!"unknown event type '{other}'"

/-- An environmental event in the browser's format. -/
def eventJson : EnvironmentEvent → Json
  | .idle => Json.mkObj [("type", "idle")]
  | .changeGravity g => Json.mkObj [("type", "setGravity"), ("value", vecJ g)]
  | .reverseGravity => Json.mkObj [("type", "reverseGravity")]
  | .disableGravity => Json.mkObj [("type", "disableGravity")]
  | .changeMaxSpeed v => Json.mkObj [("type", "setLaw"), ("law", "maxSpeed"), ("value", ratJ v)]
  | .changeMaxAcceleration a =>
    Json.mkObj [("type", "setLaw"), ("law", "maxAcceleration"), ("value", ratJ a)]
  | .changeRestitution r =>
    Json.mkObj [("type", "setLaw"), ("law", "restitution"), ("value", ratJ r)]

/-- Why `Allowed` refuses an event, in plain words. -/
def notAllowedReason : EnvironmentEvent → String
  | .changeMaxSpeed _ => "The speed limit must be above zero."
  | .changeMaxAcceleration _ => "The force limit can't be negative."
  | .changeRestitution _ => "Bounciness must be between 0 and 1."
  | _ => "This event is not allowed."

def idOf (j : Json) : Option Nat := (j.getObjValAs? Nat "id").toOption

def State.reparse (s : State) (bodies : Array Json) : Parse State := do
  let bs ← bodies.toList.mapM bodyOf
  return { s with bodies, world := { s.world with bodies := bs } }

def State.edit (s : State) : Action → Parse State
  | .spawn body => do
    let next := s.bodies.foldl (fun m j => max m ((idOf j).getD 0 + 1)) 0
    s.reparse (s.bodiesJson.push (body.setObjVal! "id" (toJson next)))
  | .remove id => s.reparse (s.bodiesJson.filter (idOf · != some id))
  | .impulse id dv => do
    let bodies ← s.bodiesJson.mapM fun j => do
      if idOf j != some id then return j
      let b ← bodyOf j
      return bodyJson { b with velocity := (b.velocity.add dv).clampAbs s.world.laws.maxSpeed } j
    s.reparse bodies
  | .setBody id p v => do
    let bodies ← s.bodiesJson.mapM fun j => do
      if idOf j != some id then return j
      let b ← bodyOf j
      return bodyJson { b with position := p.getD b.position, velocity := v.getD b.velocity } j
    s.reparse bodies
  | _ => return s

/-! ## Guarantees -/

structure Guarantee where
  id : String
  text : String
  statement : String
  theoremName : String
  assumes : String
  explanation : String
  holds : World → Bool
  /-- For guarantees about a step rather than a state: does the step from `w` with `e` keep it? -/
  stepHolds : World → EnvironmentEvent → Bool := fun _ _ => true
  /-- The theorem covers only `Allowed` events. If false, it covers every event. -/
  needsAllowed : Bool

def guarantees : List Guarantee := [
  { id := "positive-mass", text := "Every body keeps a positive mass."
    statement := "∀ b ∈ w.bodies, 0 < b.mass"
    theoremName := "step_preserves_positiveMass"
    assumes := "The run started from a world where every mass is positive. Holds for every event."
    explanation := "No event and no tick changes a body's mass, so a positive mass stays positive."
    holds := fun w => decide (PositiveMass w), needsAllowed := false },
  { id := "in-the-box", text := "Every body stays inside the box."
    statement := "∀ b ∈ w.bodies, w.bounds.Contains b.position"
    theoremName := "step_preserves_boundedPosition"
    assumes := "The run started with every body inside the box. Holds for every event."
    explanation := "Each tick moves a body, then puts it back at the nearest point of the box. \
      So no body can end a tick outside. (Bodies stop at walls; they do not bounce.)"
    holds := fun w => decide (BoundedPosition w), needsAllowed := false },
  { id := "speed-limit", text := "Nothing moves faster than the speed limit."
    statement := "∀ b ∈ w.bodies, |v.x|, |v.y|, |v.z| ≤ w.laws.maxSpeed"
    theoremName := "boundedVelocity_preservesAll"
    assumes := "Every event was allowed: the speed limit was never set to zero or below."
    explanation := "Each tick caps every velocity component at the speed limit. If the limit goes \
      negative, no velocity can meet it; negative_maxSpeed_violates_boundedVelocity proves this."
    holds := fun w => decide (BoundedVelocity w), needsAllowed := true },
  { id := "safe-environment", text := "The laws stay sensible."
    statement := "box non-empty ∧ 0 < maxSpeed ∧ 0 ≤ maxAcceleration ∧ 0 < timeStep ∧ 0 ≤ restitution ≤ 1"
    theoremName := "safeEnvironment_preservesAll"
    assumes := "Every event was allowed."
    explanation := "Allowed events only set a speed limit above zero, a force limit of zero or \
      more, and a bounciness from 0 to 1. Nothing changes the box or the time step."
    holds := fun w => decide (SafeEnvironment w), needsAllowed := true },
  { id := "bounce-no-speedup", text := "Hitting a wall never makes a body faster."
    statement := "|v_after| ≤ |v_before| on each axis, for every body on every tick"
    theoremName := "wall_never_speeds_up"
    assumes := "Nothing. It holds for every world and every event."
    explanation := "At a wall, the velocity on that axis reverses and keeps at most the bounciness \
      share of its size. tick treats a bounciness above 1 as 1, so even a bad law can't make a wall \
      add speed."
    holds := fun _ => true
    stepHolds := fun w e =>
      let w' := applyEvent w e
      decide (∀ b ∈ w'.bodies, WallNeverSpeedsUp w'.laws w'.bounds b)
    needsAllowed := false }
]

inductive Status where
  | proven | violated | unknown
  deriving BEq

def Status.name : Status → String
  | .proven => "proven" | .violated => "violated" | .unknown => "unknown"

def Status.ofName : String → Status
  | "proven" => .proven | "violated" => .violated | _ => .unknown

/-- Where one guarantee stands, as of one frame. -/
structure Track where
  status : Status
  /-- The tick this proof (or this run) starts from. -/
  since : Nat
  /-- The first tick at which a computed state broke the guarantee. -/
  violatedAt : Option Nat
  note : String

def Track.encode (t : Track) : Json :=
  Json.mkObj [("status", t.status.name), ("since", toJson t.since),
    ("violatedAt", match t.violatedAt with | some n => toJson n | none => Json.null),
    ("note", t.note)]

def Track.ofJson (j : Json) : Option Track := do
  let status ← (j.getObjValAs? String "status").toOption
  let since ← (j.getObjValAs? Nat "since").toOption
  return { status := .ofName status, since, violatedAt := (j.getObjValAs? Nat "violatedAt").toOption,
           note := (j.getObjValAs? String "note").toOption.getD "" }

/-- A guarantee checked on a new starting state. -/
def Track.start (g : Guarantee) (w : World) (tick : Nat) : Track :=
  if g.holds w then
    { status := .proven, since := tick, violatedAt := none,
      note := s!"Holds at tick {tick}, and {g.theoremName} covers every \
        {if g.needsAllowed then "allowed " else ""}event from there." }
  else
    { status := .violated, since := tick, violatedAt := some tick,
      note := s!"Fails in the state at tick {tick}." }

/-- Before an event runs: an event the theorem does not cover ends the proof. -/
def Track.onEvent (t : Track) (g : Guarantee) (w : World) (e : EnvironmentEvent) (tick : Nat) : Track :=
  if t.status != .violated && !g.stepHolds w e then
    { t with status := .violated, violatedAt := some (tick + 1),
             note := s!"The step from tick {tick} to {tick + 1}, computed by step, breaks it." }
  else if t.status == .proven && g.needsAllowed && !decide (Allowed w e) then
    { t with status := .unknown,
             note := s!"At tick {tick} an event the theorem does not cover ran. {notAllowedReason e}" }
  else t

/-- After each step: a state that breaks the guarantee is a counterexample. -/
def Track.onFrame (t : Track) (g : Guarantee) (w : World) (tick : Nat) : Track :=
  if t.status != .violated && !g.holds w then
    { t with status := .violated, violatedAt := some tick,
             note := s!"The state at tick {tick}, computed by step, breaks it." }
  else t

abbrev Tracks := List (Guarantee × Track)

def tracksJson (ts : Tracks) : Json := Json.mkObj (ts.map fun (g, t) => (g.id, t.encode))

def startTracks (w : World) (tick : Nat) : Tracks := guarantees.map fun g => (g, Track.start g w tick)

def tracksOf (j : Option Json) (s : State) : Tracks :=
  guarantees.map fun g =>
    let saved := j.bind fun j => (j.getObjVal? g.id).toOption.bind Track.ofJson
    (g, saved.getD (Track.start g s.world s.tick))

def guaranteeInfo : Json := Json.arr (guarantees.map fun g => Json.mkObj [
  ("id", g.id), ("text", g.text), ("statement", g.statement), ("theorem", g.theoremName),
  ("assumes", g.assumes), ("explanation", g.explanation), ("lean", true)]).toArray

/-! ## Random environmental events, from a seed -/

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- A whole number in `lo .. hi`, from random number `r`. -/
def pick (r : Nat) (lo hi : Int) : ℚ := (lo + ((r % (hi - lo + 1).toNat : Nat) : Int) : Int)

/-- The random event at a tick, if any. `rate` is the chance of an event on each tick. Some of
these events are not allowed (a negative speed limit), which is the point: a protected universe
rejects them, and an unprotected one shows what they break. -/
def randomEvent (seed tick : Nat) (rate : ℚ) : Option EnvironmentEvent :=
  let r1 := lcg (lcg (seed * 7919 + tick + 1))
  if rate ≤ ((r1 % 1000 : Nat) : ℚ) / 1000 then none else
  let r2 := lcg r1
  let r3 := lcg r2
  let r4 := lcg r3
  match r2 % 7 with
  | 0 => some (.changeGravity ⟨pick r3 (-15) 15, pick r4 (-30) 10, 0⟩)
  | 1 => some .reverseGravity
  | 2 => some .disableGravity
  | 3 => some (.changeMaxSpeed (pick r3 (-10) 40))
  | 4 => some (.changeMaxAcceleration (pick r3 (-10) 60))
  | 5 => some (.changeRestitution (pick r3 0 15 / 10))
  | _ => some (.changeGravity ⟨0, pick r3 (-30) (-1), 0⟩)

/-! ## A new world from a seed -/

def generateWorld (seed : Nat) : Json := Id.run do
  let mut r := lcg (seed + 17)
  let count := 5 + r % 6
  let mut bodies : Array Json := #[]
  for id in [0:count] do
    r := lcg r
    let water := r % 5 != 0
    r := lcg r
    let temperature : Int := if water then [-15, 20, 110][r % 3]! else 20
    let phase := if !water then "solid" else if temperature < 0 then "solid"
      else if temperature < 100 then "liquid" else "gas"
    let mut nums : Array Nat := #[]
    for _ in [0:7] do
      r := lcg r
      nums := nums.push r
    bodies := bodies.push (Json.mkObj [
      ("id", toJson id), ("material", if water then "water" else "rubber"), ("phase", phase),
      ("position", vecJ ⟨pick nums[0]! (-80) 80 / 10, pick nums[1]! 20 120 / 10, pick nums[2]! (-80) 80 / 10⟩),
      ("velocity", vecJ ⟨pick nums[3]! (-30) 30 / 10, pick nums[4]! 0 40 / 10, pick nums[5]! (-30) 30 / 10⟩),
      ("mass", ratJ (pick nums[6]! 1 3)), ("temperature", toString temperature)])
  return Json.mkObj [
    ("tick", toJson (0 : Nat)),
    ("bounds", Json.mkObj [("min", vecJ ⟨-10, 0, -10⟩), ("max", vecJ ⟨10, 15, 10⟩)]),
    ("laws", Json.mkObj [
      ("gravity", vecJ ⟨0, -981 / 100, 0⟩), ("maxSpeed", ratJ 30), ("maxAcceleration", ratJ 40),
      ("timeStep", ratJ (1 / 60)),
      -- Laws the browser shows but the Lean model does not have yet. They pass through unchanged.
      ("restitution", "7/10"), ("drag", "1/200"), ("freezingPoint", "0"), ("boilingPoint", "100"),
      ("ambientTemperature", "20"), ("heatTransfer", "1/100")]),
    ("bodies", Json.arr bodies)]

/-! ## One request -/

def rejection (index : Nat) (event : Json) (reason : String) (protects : Option String) : Json :=
  Json.mkObj [("index", toJson index), ("event", event), ("reason", reason),
    ("protects", match protects with | some p => Json.str p | none => Json.null)]

/-- In a protected universe, the first selected guarantee whose theorem does not cover `e`. -/
def blockedBy (selected : List String) (w : World) (e : EnvironmentEvent) : Option Guarantee :=
  if decide (Allowed w e) then none
  else guarantees.find? fun g => g.needsAllowed && selected.contains g.id

/-- Answer `POST /api/step`. -/
def stepRequest (req : Json) : Parse Json := do
  let mut s ← stateOf (← req.getObjVal? "world")
  let protect := (req.getObjValAs? String "mode").toOption == some "protected"
  let selected := (req.getObjValAs? (List String) "selected").toOption.getD []
  let ticks := min 240 ((req.getObjValAs? Nat "ticks").toOption.getD 1)
  let rate := ((req.getObjValAs? String "randomness").toOption.bind parseRat).getD 0
  let seed := (req.getObjValAs? Nat "eventSeed").toOption.getD 0
  let events := (req.getObjValAs? (Array Json) "events").toOption.getD #[]
  let mut tracks := tracksOf (req.getObjVal? "proof").toOption s
  let mut frames : Array Json := #[]
  let mut rejected : Array Json := #[]
  let mut randoms : Array Json := #[]
  let frame := fun (s : State) (ts : Tracks) => s.encode.setObjVal! "_proof" (tracksJson ts)
  -- The browser's events, in order. Each environmental event is one step.
  for i in [0:events.size] do
    let ej := events[i]!
    match actionOf ej with
    | .error msg => rejected := rejected.push (rejection i ej msg none)
    | .ok (.unsupported reason) => rejected := rejected.push (rejection i ej reason none)
    | .ok (.env e) =>
      match (if protect then blockedBy selected s.world e else none) with
      | some g =>
        rejected := rejected.push (rejection i ej
          s!"{notAllowedReason e} The proof of \"{g.text}\" covers only allowed events." (some g.id))
      | none =>
        let w := s.world
        let t := s.tick
        s := s.step e
        tracks := tracks.map fun (g, tr) => (g, (tr.onEvent g w e t).onFrame g s.world s.tick)
        frames := frames.push (frame s tracks)
    | .ok act =>
      match s.edit act with
      | .error msg => rejected := rejected.push (rejection i ej msg none)
      | .ok s' =>
        match (if protect then guarantees.find? fun g => selected.contains g.id && !g.holds s'.world
               else none) with
        | some g =>
          rejected := rejected.push (rejection i ej
            s!"This edit would break \"{g.text}\"." (some g.id))
        | none =>
          s := s'
          -- An edit makes a new starting state, so each proof starts again from here.
          tracks := startTracks s.world s.tick
  -- The remaining ticks: random events if any, otherwise time just passes.
  while frames.size < ticks do
    let mut e := EnvironmentEvent.idle
    if let some r := randomEvent seed s.tick rate then
      match (if protect then blockedBy selected s.world r else none) with
      | some g =>
        randoms := randoms.push (Json.mkObj [("tick", toJson s.tick), ("event", eventJson r),
          ("accepted", false), ("reason", s!"{notAllowedReason r} Rejected to protect \"{g.text}\".")])
      | none =>
        randoms := randoms.push (Json.mkObj [("tick", toJson s.tick), ("event", eventJson r),
          ("accepted", true)])
        e := r
    let w := s.world
    let t := s.tick
    s := s.step e
    tracks := tracks.map fun (g, tr) => (g, (tr.onEvent g w e t).onFrame g s.world s.tick)
    frames := frames.push (frame s tracks)
  return Json.mkObj [
    ("frames", Json.arr frames), ("rejected", Json.arr rejected), ("randomEvents", Json.arr randoms),
    ("guarantees", guaranteeInfo), ("engine", "lean")]

end Paradox.Api

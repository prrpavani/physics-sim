import Lean.Data.Json
import Paradox.Rules.Random
import Paradox.Verification.LawAudit
import Paradox.Consistency.Transitions

/-!
# The JSON contract

Hand-written so the wire format is simple and stable. See `shared/schemas/paradox-v1.schema.json`.

Rationals travel as strings such as `"49/10"`, so no precision is lost. Decoders also accept integers,
decimals such as `"0.5"`, and JSON numbers, which are read exactly. This layer is tested but not
proved correct; it is listed as trusted in the README.
-/

namespace Paradox.Api

open Lean (Json JsonNumber)

/-- A decoding result: the value or a message saying what was wrong. -/
abbrev Dec := Except String

/-- Read a required field. -/
def field (j : Json) (k : String) : Dec Json :=
  match j.getObjVal? k with
  | .ok v => if v.isNull then throw s!"field '{k}' is null" else pure v
  | .error _ => throw s!"missing field '{k}'"

/-- Read an optional field. -/
def optField (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok v => if v.isNull then none else some v
  | .error _ => none

/-! ## Rationals -/

/-- A rational as a string. -/
def encRat (q : ℚ) : Json :=
  if q.den = 1 then Json.str (toString q.num) else Json.str s!"{q.num}/{q.den}"

/-- Read a decimal string such as `-1.25` exactly. -/
def parseDecimal (s : String) : Option ℚ :=
  match s.splitOn "." with
  | [whole] => (whole.toInt?).map fun i => (i : ℚ)
  | [whole, frac] =>
    let neg := whole.startsWith "-"
    let w := if whole.isEmpty || whole == "-" then some (0 : Int) else whole.toInt?
    match w, frac.toNat? with
    | some w, some f =>
      let fracValue : ℚ := (f : ℚ) / ((10 ^ frac.length : Nat) : ℚ)
      some (if neg then (w : ℚ) - fracValue else (w : ℚ) + fracValue)
    | _, _ => none
  | _ => none

/-- Read a rational from a string or a JSON number. -/
def decRat (j : Json) : Dec ℚ :=
  match j with
  | .str s =>
    match s.splitOn "/" with
    | [a] =>
      match parseDecimal a with
      | some q => pure q
      | none => throw s!"bad rational '{s}'"
    | [a, b] =>
      match a.toInt?, b.toInt? with
      | some n, some d =>
        if d == 0 then throw s!"zero denominator in '{s}'" else pure ((n : ℚ) / (d : ℚ))
      | _, _ => throw s!"bad rational '{s}'"
    | _ => throw s!"bad rational '{s}'"
  | .num n => pure ((n.mantissa : ℚ) / ((10 ^ n.exponent : Nat) : ℚ))
  | _ => throw "expected a rational string or number"

/-- Read a field as a rational. -/
def ratField (j : Json) (k : String) : Dec ℚ := do decRat (← field j k)

/-- Read a field as a rational, with a default. -/
def ratFieldD (j : Json) (k : String) (d : ℚ) : Dec ℚ :=
  match optField j k with
  | some v => decRat v
  | none => pure d

/-- A natural number. -/
def decNat (j : Json) : Dec Nat :=
  match j.getNat? with
  | .ok n => pure n
  | .error _ => throw "expected a natural number"

/-- Read a list. -/
def decList {α : Type} (f : Json → Dec α) (j : Json) : Dec (List α) := do
  let arr ← j.getArr?
  return (← arr.mapM f).toList

/-- Read a field as a list, empty if absent. -/
def listFieldD {α : Type} (f : Json → Dec α) (j : Json) (k : String) (d : List α := []) :
    Dec (List α) :=
  match optField j k with
  | some v => decList f v
  | none => pure d

/-- A list as JSON. -/
def encList {α : Type} (f : α → Json) (l : List α) : Json :=
  Json.arr (l.map f).toArray

/-- The `type` tag of a tagged object. -/
def typeOf (j : Json) : Dec String := do
  match (← field j "type") with
  | .str s => pure s
  | _ => throw "'type' must be a string"

/-! ## Basic parts -/

def encVec (v : Vec3) : Json :=
  Json.mkObj [("x", encRat v.x), ("y", encRat v.y), ("z", encRat v.z)]

def decVec (j : Json) : Dec Vec3 := do
  return ⟨← ratField j "x", ← ratField j "y", ← ratField j "z"⟩

def encBounds (b : Bounds) : Json :=
  Json.mkObj [("minX", encRat b.minX), ("maxX", encRat b.maxX), ("minY", encRat b.minY),
    ("maxY", encRat b.maxY), ("minZ", encRat b.minZ), ("maxZ", encRat b.maxZ)]

def decBounds (j : Json) : Dec Bounds := do
  return ⟨← ratField j "minX", ← ratField j "maxX", ← ratField j "minY",
    ← ratField j "maxY", ← ratField j "minZ", ← ratField j "maxZ"⟩

def encShape : Shape → Json
  | .sphere r => Json.mkObj [("type", "sphere"), ("radius", encRat r)]
  | .cube h => Json.mkObj [("type", "cube"), ("halfWidth", encRat h)]

def decShape (j : Json) : Dec Shape := do
  match ← typeOf j with
  | "sphere" => return .sphere (← ratField j "radius")
  | "cube" => return .cube (← ratField j "halfWidth")
  | t => throw s!"unknown shape '{t}'"

/-- A rational as a floating-point number, for drawing only. Never use it as a formal value. -/
def approx (q : ℚ) : Json :=
  let f := Float.ofInt q.num / Float.ofNat q.den
  match JsonNumber.fromFloat? f with
  | .inr n => .num n
  | .inl _ => .null

def encBody (b : Body) : Json :=
  Json.mkObj [("id", (b.id : Nat)), ("shape", encShape b.shape), ("position", encVec b.position),
    ("velocity", encVec b.velocity), ("mass", encRat b.mass), ("charge", encRat b.charge),
    ("renderPosition", Json.arr #[approx b.position.x, approx b.position.y, approx b.position.z]),
    ("renderVelocity", Json.arr #[approx b.velocity.x, approx b.velocity.y, approx b.velocity.z]),
    ("renderSize", approx b.extent)]

def decBody (j : Json) : Dec Body := do
  return { id := ← decNat (← field j "id")
           shape := ← match optField j "shape" with
             | some s => decShape s
             | none => pure (.sphere (1 / 2))
           position := ← decVec (← field j "position")
           velocity := ← match optField j "velocity" with
             | some v => decVec v
             | none => pure Vec3.zero
           mass := ← ratFieldD j "mass" 1
           charge := ← ratFieldD j "charge" 0 }

/-! ## Laws -/

def encTopology : Topology → Json
  | .box => "box"
  | .torus => "torus"

def decTopology : Json → Dec Topology
  | .str "box" => pure .box
  | .str "torus" => pure .torus
  | _ => throw "topology must be 'box' or 'torus'"

def encMetric : Metric → Json
  | .euclidean => "euclidean"
  | .manhattan => "manhattan"
  | .chebyshev => "chebyshev"

def decMetric : Json → Dec Metric
  | .str "euclidean" => pure .euclidean
  | .str "manhattan" => pure .manhattan
  | .str "chebyshev" => pure .chebyshev
  | _ => throw "metric must be 'euclidean', 'manhattan' or 'chebyshev'"

def encCollision : CollisionMode → Json
  | .none => "none"
  | .bounce => "bounce"
  | .exchangeVelocity => "exchangeVelocity"
  | .exchangeMass => "exchangeMass"
  | .merge => "merge"
  | .spawn => "spawn"

def decCollision : Json → Dec CollisionMode
  | .str "none" => pure .none
  | .str "bounce" => pure .bounce
  | .str "exchangeVelocity" => pure .exchangeVelocity
  | .str "exchangeMass" => pure .exchangeMass
  | .str "merge" => pure .merge
  | .str "spawn" => pure .spawn
  | _ => throw "unknown collision mode"

def encExpr : LawExpr → Json
  | .const q => Json.mkObj [("type", "const"), ("value", encRat q)]
  | .massA => Json.mkObj [("type", "massA")]
  | .massB => Json.mkObj [("type", "massB")]
  | .chargeA => Json.mkObj [("type", "chargeA")]
  | .chargeB => Json.mkObj [("type", "chargeB")]
  | .distSquared => Json.mkObj [("type", "distSquared")]
  | .dist => Json.mkObj [("type", "dist")]
  | .speedSquared => Json.mkObj [("type", "speedSquared")]
  | .add a b => Json.mkObj [("type", "add"), ("a", encExpr a), ("b", encExpr b)]
  | .sub a b => Json.mkObj [("type", "sub"), ("a", encExpr a), ("b", encExpr b)]
  | .mul a b => Json.mkObj [("type", "mul"), ("a", encExpr a), ("b", encExpr b)]
  | .div a b => Json.mkObj [("type", "div"), ("a", encExpr a), ("b", encExpr b)]
  | .neg a => Json.mkObj [("type", "neg"), ("a", encExpr a)]
  | .pow a n => Json.mkObj [("type", "pow"), ("a", encExpr a), ("n", (n : Nat))]

partial def decExpr (j : Json) : Dec LawExpr := do
  match ← typeOf j with
  | "const" => return .const (← ratField j "value")
  | "massA" => return .massA
  | "massB" => return .massB
  | "chargeA" => return .chargeA
  | "chargeB" => return .chargeB
  | "distSquared" => return .distSquared
  | "dist" => return .dist
  | "speedSquared" => return .speedSquared
  | "add" => return .add (← decExpr (← field j "a")) (← decExpr (← field j "b"))
  | "sub" => return .sub (← decExpr (← field j "a")) (← decExpr (← field j "b"))
  | "mul" => return .mul (← decExpr (← field j "a")) (← decExpr (← field j "b"))
  | "div" => return .div (← decExpr (← field j "a")) (← decExpr (← field j "b"))
  | "neg" => return .neg (← decExpr (← field j "a"))
  | "pow" => return .pow (← decExpr (← field j "a")) (← decNat (← field j "n"))
  | t => throw s!"unknown formula '{t}'"

def encField (f : Field) : Json :=
  Json.mkObj [("region", encBounds f.region), ("acceleration", encVec f.acceleration)]

def decField (j : Json) : Dec Field := do
  return ⟨← decBounds (← field j "region"), ← decVec (← field j "acceleration")⟩

def encRegion (r : Region) : Json :=
  Json.mkObj [("name", r.name), ("color", r.color), ("box", encBounds r.box),
    ("timeScale", encRat r.timeScale)]

def decStr (j : Json) : Dec String :=
  match j with
  | .str s => pure s
  | _ => throw "expected a string"

def decRegion (j : Json) : Dec Region := do
  return { name := ← decStr (← field j "name")
           color := match optField j "color" with
             | some (.str c) => c
             | _ => ""
           box := ← decBounds (← field j "box")
           timeScale := ← ratFieldD j "timeScale" 1 }

def encEffect : PortalEffect → Json
  | .none => Json.mkObj [("type", "none")]
  | .reverse => Json.mkObj [("type", "reverse")]
  | .rotate => Json.mkObj [("type", "rotate")]
  | .scale k => Json.mkObj [("type", "scale"), ("factor", encRat k)]

def decEffect (j : Json) : Dec PortalEffect := do
  match ← typeOf j with
  | "none" => return .none
  | "reverse" => return .reverse
  | "rotate" => return .rotate
  | "scale" => return .scale (← ratField j "factor")
  | t => throw s!"unknown portal effect '{t}'"

def encPortal (p : Portal) : Json :=
  Json.mkObj [("entrance", encBounds p.entrance),
    ("exit", match p.exit with
      | some e => encVec e
      | none => Json.null),
    ("effect", encEffect p.effect)]

def decPortal (j : Json) : Dec Portal := do
  return { entrance := ← decBounds (← field j "entrance")
           exit := ← match optField j "exit" with
             | some e => some <$> decVec e
             | none => pure none
           effect := ← match optField j "effect" with
             | some e => decEffect e
             | none => pure .none }

def encLaws (l : PhysicsLaws) : Json :=
  Json.mkObj [("gravity", encVec l.gravity), ("fields", encList encField l.fields),
    ("maxSpeed", encRat l.maxSpeed), ("maxAcceleration", encRat l.maxAcceleration),
    ("timeStep", encRat l.timeStep), ("restitution", encRat l.restitution),
    ("pairForce", encExpr l.pairForce), ("reaction", encRat l.reaction),
    ("drag", encExpr l.drag), ("central", encExpr l.central),
    ("magnetic", encVec l.magnetic), ("massRate", encRat l.massRate),
    ("topology", encTopology l.topology), ("metric", encMetric l.metric),
    ("collisions", encCollision l.collisions), ("populationLimit", (l.populationLimit : Nat)),
    ("grid", (l.grid : Nat))]

/-- Read laws. Any missing field takes its default, so clients can send only what they change. -/
def decLaws (j : Json) : Dec PhysicsLaws := do
  let d := defaultLaws
  let opt {α : Type} (k : String) (f : Json → Dec α) (dflt : α) : Dec α :=
    match optField j k with
    | some v => f v
    | none => pure dflt
  return { gravity := ← opt "gravity" decVec d.gravity
           fields := ← listFieldD decField j "fields"
           maxSpeed := ← ratFieldD j "maxSpeed" d.maxSpeed
           maxAcceleration := ← ratFieldD j "maxAcceleration" d.maxAcceleration
           timeStep := ← ratFieldD j "timeStep" d.timeStep
           restitution := ← ratFieldD j "restitution" d.restitution
           pairForce := ← opt "pairForce" decExpr d.pairForce
           reaction := ← ratFieldD j "reaction" d.reaction
           drag := ← opt "drag" decExpr d.drag
           central := ← opt "central" decExpr d.central
           magnetic := ← opt "magnetic" decVec d.magnetic
           massRate := ← ratFieldD j "massRate" d.massRate
           topology := ← opt "topology" decTopology d.topology
           metric := ← opt "metric" decMetric d.metric
           collisions := ← opt "collisions" decCollision d.collisions
           populationLimit := ← opt "populationLimit" decNat d.populationLimit
           grid := ← opt "grid" decNat d.grid }

/-! ## Rules -/

def encBodyCond : BodyCond → Json
  | .all => Json.mkObj [("type", "all")]
  | .inBox b => Json.mkObj [("type", "inBox"), ("box", encBounds b)]
  | .entersBox b => Json.mkObj [("type", "entersBox"), ("box", encBounds b)]
  | .inRegion n => Json.mkObj [("type", "inRegion"), ("name", n)]
  | .onColor c => Json.mkObj [("type", "onColor"), ("color", c)]
  | .speedAbove s => Json.mkObj [("type", "speedAbove"), ("speed", encRat s)]
  | .not c => Json.mkObj [("type", "not"), ("condition", encBodyCond c)]

partial def decBodyCond (j : Json) : Dec BodyCond := do
  match ← typeOf j with
  | "all" => return .all
  | "inBox" => return .inBox (← decBounds (← field j "box"))
  | "entersBox" => return .entersBox (← decBounds (← field j "box"))
  | "inRegion" => return .inRegion (← decStr (← field j "name"))
  | "onColor" => return .onColor (← decStr (← field j "color"))
  | "speedAbove" => return .speedAbove (← ratField j "speed")
  | "not" => return .not (← decBodyCond (← field j "condition"))
  | t => throw s!"unknown body condition '{t}'"

def encBodyAction : BodyAction → Json
  | .applyForce f => Json.mkObj [("type", "applyForce"), ("force", encVec f)]
  | .reverseVelocity => Json.mkObj [("type", "reverseVelocity")]
  | .rotateVelocity => Json.mkObj [("type", "rotateVelocity")]
  | .scaleVelocity k => Json.mkObj [("type", "scaleVelocity"), ("factor", encRat k)]
  | .clampVelocity => Json.mkObj [("type", "clampVelocity")]
  | .translate d => Json.mkObj [("type", "translate"), ("by", encVec d)]
  | .clampPosition => Json.mkObj [("type", "clampPosition")]
  | .scaleMass k => Json.mkObj [("type", "scaleMass"), ("factor", encRat k)]
  | .setMassFormula f => Json.mkObj [("type", "setMassFormula"), ("formula", encExpr f)]
  | .setCharge q => Json.mkObj [("type", "setCharge"), ("charge", encRat q)]

def decBodyAction (j : Json) : Dec BodyAction := do
  match ← typeOf j with
  | "applyForce" => return .applyForce (← decVec (← field j "force"))
  | "reverseVelocity" => return .reverseVelocity
  | "rotateVelocity" => return .rotateVelocity
  | "scaleVelocity" => return .scaleVelocity (← ratField j "factor")
  | "clampVelocity" => return .clampVelocity
  | "translate" => return .translate (← decVec (← field j "by"))
  | "clampPosition" => return .clampPosition
  | "scaleMass" => return .scaleMass (← ratField j "factor")
  | "setMassFormula" => return .setMassFormula (← decExpr (← field j "formula"))
  | "setCharge" => return .setCharge (← ratField j "charge")
  | t => throw s!"unknown body action '{t}'"

def encWorldCond : WorldCond → Json
  | .always => Json.mkObj [("type", "always")]
  | .gravityAbove g => Json.mkObj [("type", "gravityAbove"), ("value", encRat g)]
  | .gravityChanged => Json.mkObj [("type", "gravityChanged")]
  | .everyTicks n => Json.mkObj [("type", "everyTicks"), ("n", (n : Nat))]
  | .not c => Json.mkObj [("type", "not"), ("condition", encWorldCond c)]

partial def decWorldCond (j : Json) : Dec WorldCond := do
  match ← typeOf j with
  | "always" => return .always
  | "gravityAbove" => return .gravityAbove (← ratField j "value")
  | "gravityChanged" => return .gravityChanged
  | "everyTicks" => return .everyTicks (← decNat (← field j "n"))
  | "not" => return .not (← decWorldCond (← field j "condition"))
  | t => throw s!"unknown world condition '{t}'"

def encWorldAction : WorldAction → Json
  | .setGravity g => Json.mkObj [("type", "setGravity"), ("gravity", encVec g)]
  | .reverseGravity => Json.mkObj [("type", "reverseGravity")]
  | .setMaxSpeed v => Json.mkObj [("type", "setMaxSpeed"), ("value", encRat v)]
  | .setPairForce f => Json.mkObj [("type", "setPairForce"), ("formula", encExpr f)]
  | .setReaction r => Json.mkObj [("type", "setReaction"), ("value", encRat r)]
  | .setMassRate r => Json.mkObj [("type", "setMassRate"), ("value", encRat r)]

def decWorldAction (j : Json) : Dec WorldAction := do
  match ← typeOf j with
  | "setGravity" => return .setGravity (← decVec (← field j "gravity"))
  | "reverseGravity" => return .reverseGravity
  | "setMaxSpeed" => return .setMaxSpeed (← ratField j "value")
  | "setPairForce" => return .setPairForce (← decExpr (← field j "formula"))
  | "setReaction" => return .setReaction (← ratField j "value")
  | "setMassRate" => return .setMassRate (← ratField j "value")
  | t => throw s!"unknown world action '{t}'"

def encRule : Rule → Json
  | .skip => Json.mkObj [("type", "skip")]
  | .body c a =>
    Json.mkObj [("type", "body"), ("condition", encBodyCond c), ("action", encBodyAction a)]
  | .world a => Json.mkObj [("type", "world"), ("action", encWorldAction a)]
  | .destroy c => Json.mkObj [("type", "destroy"), ("condition", encBodyCond c)]
  | .create t => Json.mkObj [("type", "create"), ("template", encBody t)]
  | .seq a b => Json.mkObj [("type", "seq"), ("first", encRule a), ("then", encRule b)]
  | .when c r => Json.mkObj [("type", "when"), ("condition", encWorldCond c), ("rule", encRule r)]

partial def decRule (j : Json) : Dec Rule := do
  match ← typeOf j with
  | "skip" => return .skip
  | "body" =>
    let c ← match optField j "condition" with
      | some c => decBodyCond c
      | none => pure .all
    return .body c (← decBodyAction (← field j "action"))
  | "world" => return .world (← decWorldAction (← field j "action"))
  | "destroy" => return .destroy (← decBodyCond (← field j "condition"))
  | "create" => return .create (← decBody (← field j "template"))
  | "seq" => return .seq (← decRule (← field j "first")) (← decRule (← field j "then"))
  | "when" => return .when (← decWorldCond (← field j "condition")) (← decRule (← field j "rule"))
  | t => throw s!"unknown rule '{t}'"

/-! ## Worlds -/

def encWorld (w : World) : Json :=
  Json.mkObj [("bodies", encList encBody w.bodies), ("bounds", encBounds w.bounds),
    ("laws", encLaws w.laws), ("regions", encList encRegion w.regions),
    ("portals", encList encPortal w.portals), ("rules", encList encRule w.rules),
    ("tick", (w.tick : Nat)), ("nextId", (w.nextId : Nat))]

/-- Read a world. Missing parts take defaults. A missing `nextId` is set above every id in use. -/
def decWorld (j : Json) : Dec World := do
  let bodies ← listFieldD decBody j "bodies"
  let nextFree := bodies.foldl (fun m b => max m (b.id + 1)) 0
  return { bodies
           bounds := ← match optField j "bounds" with
             | some b => decBounds b
             | none => pure defaultBounds
           laws := ← match optField j "laws" with
             | some l => decLaws l
             | none => pure defaultLaws
           regions := ← listFieldD decRegion j "regions"
           portals := ← listFieldD decPortal j "portals"
           rules := ← listFieldD decRule j "rules"
           tick := ← match optField j "tick" with
             | some t => decNat t
             | none => pure 0
           nextId := ← match optField j "nextId" with
             | some n => decNat n
             | none => pure nextFree }

/-! ## Events -/

def encEvent : EnvironmentEvent → Json
  | .idle => Json.mkObj [("type", "idle")]
  | .changeGravity g => Json.mkObj [("type", "changeGravity"), ("gravity", encVec g)]
  | .reverseGravity => Json.mkObj [("type", "reverseGravity")]
  | .disableGravity => Json.mkObj [("type", "disableGravity")]
  | .changeMaxSpeed v => Json.mkObj [("type", "changeMaxSpeed"), ("value", encRat v)]
  | .changeMaxAcceleration a => Json.mkObj [("type", "changeMaxAcceleration"), ("value", encRat a)]
  | .changeRestitution e => Json.mkObj [("type", "changeRestitution"), ("value", encRat e)]
  | .changeTimeStep d => Json.mkObj [("type", "changeTimeStep"), ("value", encRat d)]
  | .changeBounds b => Json.mkObj [("type", "changeBounds"), ("bounds", encBounds b)]
  | .addField f => Json.mkObj [("type", "addField"), ("field", encField f)]
  | .clearFields => Json.mkObj [("type", "clearFields")]
  | .setPairForce f => Json.mkObj [("type", "setPairForce"), ("formula", encExpr f)]
  | .setReaction r => Json.mkObj [("type", "setReaction"), ("value", encRat r)]
  | .setDrag f => Json.mkObj [("type", "setDrag"), ("formula", encExpr f)]
  | .setCentral f => Json.mkObj [("type", "setCentral"), ("formula", encExpr f)]
  | .setMagnetic b => Json.mkObj [("type", "setMagnetic"), ("field", encVec b)]
  | .setMassRate r => Json.mkObj [("type", "setMassRate"), ("value", encRat r)]
  | .setTopology t => Json.mkObj [("type", "setTopology"), ("topology", encTopology t)]
  | .setMetric m => Json.mkObj [("type", "setMetric"), ("metric", encMetric m)]
  | .setCollisions m => Json.mkObj [("type", "setCollisions"), ("mode", encCollision m)]
  | .setPopulationLimit n => Json.mkObj [("type", "setPopulationLimit"), ("value", (n : Nat))]
  | .setGrid n => Json.mkObj [("type", "setGrid"), ("value", (n : Nat))]
  | .reverseTime => Json.mkObj [("type", "reverseTime")]
  | .spawnBody b => Json.mkObj [("type", "spawnBody"), ("body", encBody b)]
  | .removeBody i => Json.mkObj [("type", "removeBody"), ("id", (i : Nat))]
  | .applyImpulse i d =>
    Json.mkObj [("type", "applyImpulse"), ("id", (i : Nat)), ("impulse", encVec d)]
  | .setBodyState i p v =>
    Json.mkObj [("type", "setBodyState"), ("id", (i : Nat)), ("position", encVec p),
      ("velocity", encVec v)]
  | .addRegion r => Json.mkObj [("type", "addRegion"), ("region", encRegion r)]
  | .clearRegions => Json.mkObj [("type", "clearRegions")]
  | .addPortal p => Json.mkObj [("type", "addPortal"), ("portal", encPortal p)]
  | .clearPortals => Json.mkObj [("type", "clearPortals")]
  | .addRule r => Json.mkObj [("type", "addRule"), ("rule", encRule r)]
  | .clearRules => Json.mkObj [("type", "clearRules")]

def decEvent (j : Json) : Dec EnvironmentEvent := do
  match ← typeOf j with
  | "idle" => return .idle
  | "changeGravity" => return .changeGravity (← decVec (← field j "gravity"))
  | "reverseGravity" => return .reverseGravity
  | "disableGravity" => return .disableGravity
  | "changeMaxSpeed" => return .changeMaxSpeed (← ratField j "value")
  | "changeMaxAcceleration" => return .changeMaxAcceleration (← ratField j "value")
  | "changeRestitution" => return .changeRestitution (← ratField j "value")
  | "changeTimeStep" => return .changeTimeStep (← ratField j "value")
  | "changeBounds" => return .changeBounds (← decBounds (← field j "bounds"))
  | "addField" => return .addField (← decField (← field j "field"))
  | "clearFields" => return .clearFields
  | "setPairForce" => return .setPairForce (← decExpr (← field j "formula"))
  | "setReaction" => return .setReaction (← ratField j "value")
  | "setDrag" => return .setDrag (← decExpr (← field j "formula"))
  | "setCentral" => return .setCentral (← decExpr (← field j "formula"))
  | "setMagnetic" => return .setMagnetic (← decVec (← field j "field"))
  | "setMassRate" => return .setMassRate (← ratField j "value")
  | "setTopology" => return .setTopology (← decTopology (← field j "topology"))
  | "setMetric" => return .setMetric (← decMetric (← field j "metric"))
  | "setCollisions" => return .setCollisions (← decCollision (← field j "mode"))
  | "setPopulationLimit" => return .setPopulationLimit (← decNat (← field j "value"))
  | "setGrid" => return .setGrid (← decNat (← field j "value"))
  | "reverseTime" => return .reverseTime
  | "spawnBody" => return .spawnBody (← decBody (← field j "body"))
  | "removeBody" => return .removeBody (← decNat (← field j "id"))
  | "applyImpulse" => return .applyImpulse (← decNat (← field j "id")) (← decVec (← field j "impulse"))
  | "setBodyState" =>
    return .setBodyState (← decNat (← field j "id")) (← decVec (← field j "position"))
      (← decVec (← field j "velocity"))
  | "addRegion" => return .addRegion (← decRegion (← field j "region"))
  | "clearRegions" => return .clearRegions
  | "addPortal" => return .addPortal (← decPortal (← field j "portal"))
  | "clearPortals" => return .clearPortals
  | "addRule" => return .addRule (← decRule (← field j "rule"))
  | "clearRules" => return .clearRules
  | t => throw s!"unknown event '{t}'"

/-! ## Claims, constraints and results -/

def encProperty : Property → Json
  | .positiveMass => "positiveMass"
  | .boundedPosition => "boundedPosition"
  | .boundedVelocity => "boundedVelocity"
  | .safeEnvironment => "safeEnvironment"
  | .uniqueIds => "uniqueIds"

def decProperty : Json → Dec Property
  | .str "positiveMass" => pure .positiveMass
  | .str "boundedPosition" => pure .boundedPosition
  | .str "boundedVelocity" => pure .boundedVelocity
  | .str "safeEnvironment" => pure .safeEnvironment
  | .str "uniqueIds" => pure .uniqueIds
  | _ => throw "unknown property"

def encCmp : Cmp → Json
  | .lt => "lt" | .le => "le" | .eq => "eq" | .ge => "ge" | .gt => "gt"

def decCmp : Json → Dec Cmp
  | .str "lt" => pure .lt
  | .str "le" => pure .le
  | .str "eq" => pure .eq
  | .str "ge" => pure .ge
  | .str "gt" => pure .gt
  | _ => throw "comparison must be lt, le, eq, ge or gt"

def encBodyQuantity : BodyQuantity → Json
  | .mass => "mass" | .charge => "charge" | .extent => "extent"
  | .positionX => "positionX" | .positionY => "positionY" | .positionZ => "positionZ"
  | .velocityX => "velocityX" | .velocityY => "velocityY" | .velocityZ => "velocityZ"
  | .speedSquared => "speedSquared"

def decBodyQuantity : Json → Dec BodyQuantity
  | .str "mass" => pure .mass
  | .str "charge" => pure .charge
  | .str "extent" => pure .extent
  | .str "positionX" => pure .positionX
  | .str "positionY" => pure .positionY
  | .str "positionZ" => pure .positionZ
  | .str "velocityX" => pure .velocityX
  | .str "velocityY" => pure .velocityY
  | .str "velocityZ" => pure .velocityZ
  | .str "speedSquared" => pure .speedSquared
  | _ => throw "unknown body quantity"

def encLawQuantity : LawQuantity → Json
  | .gravityX => "gravityX" | .gravityY => "gravityY" | .gravityZ => "gravityZ"
  | .maxSpeed => "maxSpeed" | .maxAcceleration => "maxAcceleration"
  | .restitution => "restitution" | .timeStep => "timeStep"
  | .massRate => "massRate" | .reaction => "reaction"

def decLawQuantity : Json → Dec LawQuantity
  | .str "gravityX" => pure .gravityX
  | .str "gravityY" => pure .gravityY
  | .str "gravityZ" => pure .gravityZ
  | .str "maxSpeed" => pure .maxSpeed
  | .str "maxAcceleration" => pure .maxAcceleration
  | .str "restitution" => pure .restitution
  | .str "timeStep" => pure .timeStep
  | .str "massRate" => pure .massRate
  | .str "reaction" => pure .reaction
  | _ => throw "unknown law quantity"

def encConstraint : Constraint → Json
  | .body q c v =>
    Json.mkObj [("type", "body"), ("quantity", encBodyQuantity q), ("cmp", encCmp c),
      ("value", encRat v)]
  | .population c v => Json.mkObj [("type", "population"), ("cmp", encCmp c), ("value", encRat v)]
  | .law q c v =>
    Json.mkObj [("type", "law"), ("quantity", encLawQuantity q), ("cmp", encCmp c),
      ("value", encRat v)]

def decConstraint (j : Json) : Dec Constraint := do
  match ← typeOf j with
  | "body" =>
    return .body (← decBodyQuantity (← field j "quantity")) (← decCmp (← field j "cmp"))
      (← ratField j "value")
  | "population" => return .population (← decCmp (← field j "cmp")) (← ratField j "value")
  | "law" =>
    return .law (← decLawQuantity (← field j "quantity")) (← decCmp (← field j "cmp"))
      (← ratField j "value")
  | t => throw s!"unknown constraint '{t}'"

def encClaim : Claim → Json
  | .property p => Json.mkObj [("type", "property"), ("property", encProperty p)]
  | .constraint c => Json.mkObj [("type", "constraint"), ("constraint", encConstraint c)]
  | .momentumConserved d => Json.mkObj [("type", "momentumConserved"), ("direction", encVec d)]
  | .energyNotRising => Json.mkObj [("type", "energyNotRising")]
  | .massConserved => Json.mkObj [("type", "massConserved")]
  | .populationConserved => Json.mkObj [("type", "populationConserved")]

def decClaim (j : Json) : Dec Claim := do
  match j with
  | .str _ => return .property (← decProperty j)
  | _ =>
    match ← typeOf j with
    | "property" => return .property (← decProperty (← field j "property"))
    | "constraint" => return .constraint (← decConstraint (← field j "constraint"))
    | "momentumConserved" => return .momentumConserved (← decVec (← field j "direction"))
    | "energyNotRising" => return .energyNotRising
    | "massConserved" => return .massConserved
    | "populationConserved" => return .populationConserved
    | t => throw s!"unknown claim '{t}'"

def encScope : EventScope → Json
  | .allowed => "allowed"
  | .any => "any"
  | .timeOnly => "timeOnly"

def decScope : Json → Dec EventScope
  | .str "allowed" => pure .allowed
  | .str "any" => pure .any
  | .str "timeOnly" => pure .timeOnly
  | _ => throw "scope must be 'allowed', 'any' or 'timeOnly'"

def encStatus : Status → Json
  | .proven => "proven"
  | .counterexample => "counterexample"
  | .unknown => "unknown"
  | .underspecified => "underspecified"
  | .inconsistent => "inconsistent"

def encTrace (t : WorldTrace) : Json :=
  Json.mkObj [("initial", encWorld t.initial), ("events", encList encEvent t.events),
    ("states", encList encWorld t.states), ("final", encWorld t.final)]

def decTrace (j : Json) : Dec WorldTrace := do
  return ⟨← decWorld (← field j "initial"), ← listFieldD decEvent j "events",
    ← listFieldD decWorld j "states"⟩

def encVerdict (v : Verdict) : Json :=
  Json.mkObj [("claim", encClaim v.claim), ("status", encStatus v.status),
    ("theoremId", match v.theoremId with
      | some t => Json.str t
      | none => Json.null),
    ("assumptions", encList Json.str v.assumptions),
    ("scope", match v.scope with
      | some s => encScope s
      | none => Json.null),
    ("explanation", v.explanation),
    ("counterexample", match v.counterexample with
      | some t => encTrace t
      | none => Json.null)]

def encDecision : Decision → Json
  | .accepted e => Json.mkObj [("result", "accepted"), ("event", encEvent e)]
  | .repaired a b =>
    Json.mkObj [("result", "repaired"), ("original", encEvent a), ("event", encEvent b)]
  | .rejected e => Json.mkObj [("result", "rejected"), ("event", encEvent e)]

/-- Read search limits. Values above the caps are lowered to the caps. -/
def decLimits (j : Json) : Dec SearchLimits := do
  let d : SearchLimits := {}
  let get (k : String) (dflt cap : Nat) : Dec Nat :=
    match optField j k with
    | some v => do return min (← decNat v) cap
    | none => pure (min dflt cap)
  return { depth := ← get "depth" d.depth 5
           budget := ← get "budget" d.budget 20000
           idleSteps := ← get "idleSteps" d.idleSteps 2000 }

end Paradox.Api

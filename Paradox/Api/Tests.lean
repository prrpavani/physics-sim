import Paradox.Api.Routes
import Paradox.Verification.Examples

/-!
# Tests of the JSON contract and the router
-/

namespace Paradox.Api

open Lean (Json)

/-- A world with some of everything. -/
def fullWorld : World :=
  { testWorld [testBody 0 ⟨1 / 3, -2, 0⟩ ⟨1 / 7, 0, 3⟩ (5 / 2)]
      { testLaws with
        pairForce := strangeLaw
        drag := .const (1 / 10)
        topology := .torus
        metric := .chebyshev
        collisions := .merge
        fields := [⟨defaultBounds, ⟨1, 2, 3⟩⟩] }
    with
    regions := [⟨"r", "red", defaultBounds, 1 / 2⟩]
    portals := [⟨defaultBounds, none, .scale 2⟩, ⟨defaultBounds, some ⟨1, 1, 1⟩, .rotate⟩]
    rules := [.seq (.when .gravityChanged (.body (.not (.onColor "red")) .clampVelocity))
      (.world (.setPairForce .dist))]
    tick := 9 }

-- Everything survives a round trip through the wire format, exactly.
#guard (decWorld (encWorld fullWorld)).toOption == some fullWorld
#guard (decWorld (Json.parse (encWorld fullWorld).compress |>.toOption |>.getD .null)).toOption == some fullWorld
#guard ([.idle, .setPairForce strangeLaw, .addRule (.create (testBody 3 ⟨0, 0, 0⟩ Vec3.zero)),
    .addPortal ⟨defaultBounds, none, .reverse⟩, .setCollisions .spawn, .setBodyState 1 ⟨1, 2, 3⟩ ⟨4, 5, 6⟩] :
    List EnvironmentEvent).all fun e => (decEvent (encEvent e)).toOption == some e

-- Rationals are read exactly, in every accepted form.
#guard (decRat (Json.str "49/10")).toOption == some (49 / 10)
#guard (decRat (Json.str "-3")).toOption == some (-3)
#guard (decRat (Json.str "0.1")).toOption == some (1 / 10)
#guard (decRat (Json.str "-1.25")).toOption == some (-5 / 4)
#guard (decRat (Json.num ⟨15, 1⟩)).toOption == some (3 / 2)
#guard (decRat (Json.str "1/0")).toOption == none
#guard (decRat (Json.str "abc")).toOption == none
#guard encRat (49 / 10) == Json.str "49/10"
#guard encRat 3 == Json.str "3"

/-- The HTTP status of a request. -/
def codeOf (method path body : String) : Nat :=
  (handle method path body).code

/-- A field of the answer to a request. -/
def answer (path : String) (body : Json) (key : String) : Json :=
  ((handle "POST" path body.compress).body.getObjVal? key).toOption.getD .null

#guard codeOf "GET" "/api/health" "" == 200
#guard codeOf "GET" "/nope" "" == 404
#guard codeOf "POST" "/api/universe/step" "not json" == 400
#guard codeOf "POST" "/api/universe/step" "{}" == 400
#guard codeOf "POST" "/api/universe/create" "{\"preset\":\"nope\"}" == 400

-- Every preset starts with its guarantees intact, and every route answers.
#guard presets.all fun p => decide (Guaranteed (presetWorld p 42))
#guard presets.all fun p =>
  answer "/api/universe/create" (Json.mkObj [("preset", p.name), ("seed", (5 : Nat))]) "guaranteed"
    == Json.bool true
#guard (presets.map (·.name)).length == 20

/-- A stepping request. -/
def stepRequest (e : EnvironmentEvent) (mode : String) : Json :=
  Json.mkObj [("world", encWorld oneBody), ("event", encEvent e), ("mode", mode)]

-- Unprotected mode reports the broken guarantee; protected mode rejects the event.
#guard answer "/api/universe/step" (stepRequest (.changeMaxSpeed (-1)) "unprotected") "violations" ==
  Json.arr #["boundedVelocity", "safeEnvironment"]
#guard answer "/api/universe/step" (stepRequest (.changeMaxSpeed (-1)) "protected") "violations" ==
  Json.arr #[]

-- Limits are enforced.
#guard codeOf "POST" "/api/universe/run"
  (Json.mkObj [("world", encWorld oneBody), ("steps", (100000 : Nat))]).compress == 400

-- Work limits hold, and lowering search limits still leaves a working search.
#guard (fitLimits (testWorld ((List.range 200).map fun i => testBody i ⟨0, 0, 0⟩ Vec3.zero)) {}).budget == 1
#guard (fitLimits oneBody {}).budget == 2000

/-- A formula with too many stacked powers. -/
def towerFormula : LawExpr :=
  .pow (.pow (.pow .dist 16) 16) 16

#guard !formulaOk towerFormula
#guard codeOf "POST" "/api/universe/step" (stepRequest (.setPairForce towerFormula) "protected").compress == 400

end Paradox.Api

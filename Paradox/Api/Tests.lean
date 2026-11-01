import Paradox.Api.Routes
import Paradox.Verification.Examples

/-!
# Tests of the wire format and the routes
-/

namespace Paradox.Api

open Lean (Json)

-- Everything survives a round trip through the wire format, exactly.
#guard (decWorld (encWorld startWorld)).toOption == some startWorld
#guard (decWorld (Json.parse (encWorld startWorld).compress |>.toOption |>.getD .null)).toOption == some startWorld

-- Rationals are read exactly, in every accepted form, and bad ones are refused.
#guard (decRat (Json.str "49/10")).toOption == some (49 / 10)
#guard (decRat (Json.str "-3")).toOption == some (-3)
#guard (decRat (Json.str "0.1")).toOption == some (1 / 10)
#guard (decRat (Json.str "-1.25")).toOption == some (-5 / 4)
#guard (decRat (Json.num ⟨15, 1⟩)).toOption == some (3 / 2)
#guard (decRat (Json.str "1/0")).toOption == none
#guard (decRat (Json.str "abc")).toOption == none
#guard encRat (49 / 10) == Json.str "49/10"

/-- The HTTP status of a request. -/
def codeOf (method path body : String) : Nat :=
  (handle method path body []).code

/-- A field of the answer to a run request. -/
def runField (laws : Laws) (locked : Bool) (key : String) : Json :=
  let req := Json.mkObj [("world", encWorld startWorld), ("steps", (2 : Nat)), ("locked", Json.bool locked),
    ("laws", encLaws laws)]
  ((handle "POST" "/api/run" req.compress []).body.getObjVal? key).toOption.getD .null

#guard codeOf "POST" "/api/create" "" == 200
#guard codeOf "GET" "/nope" "" == 404
#guard codeOf "POST" "/api/run" "not json" == 400
#guard codeOf "POST" "/api/run" "{}" == 400
#guard codeOf "POST" "/api/run"
  (Json.mkObj [("world", encWorld startWorld), ("steps", (100000 : Nat)), ("locked", Json.bool true)]).compress == 400

-- The lock answers through the API, and an invalid universe is refused by the verdict route.
#guard runField { startLaws with multiplier := 100 } true "decision" == "repaired"
#guard runField { startLaws with multiplier := 100 } false "decision" == "accepted"
#guard runField { startLaws with maxSpeed := -1 } true "decision" == "refused"
#guard codeOf "POST" "/api/verdicts"
  (Json.mkObj [("world", encWorld { startWorld with laws.maxSpeed := -1 })]).compress == 400

-- Each theorem's text is found in the source, and only that theorem's block.
def sampleSource : String :=
  "/-- First. -/\ntheorem alpha : True := trivial\n\n/-- Second. -/\ntheorem beta : True := trivial"

#guard proofBlock sampleSource "Paradox.beta" == some "/-- Second. -/\ntheorem beta : True := trivial"
#guard proofBlock sampleSource "gamma" == none

end Paradox.Api

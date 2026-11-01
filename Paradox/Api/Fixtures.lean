import Paradox.Api.Routes

/-!
# Fixtures for frontend development

Every fixture is a real request and the real answer from the formal model, so a mock backend built
from them cannot drift from the contract. `make fixtures` regenerates them.
-/

namespace Paradox.Api

open Lean (Json)

/-- The spec's first demonstration: one moving object, unusual gravity, a speed limit of 10. -/
def speedWorld (rules : List Rule) : World :=
  { bodies := [{ id := 0, shape := .sphere (1 / 2), position := ⟨0, 0, 0⟩, velocity := ⟨1, 0, 0⟩,
                 mass := 1, charge := 0 }]
    bounds := defaultBounds
    laws := { defaultLaws with gravity := ⟨0, 2, 0⟩, maxSpeed := 10 }
    regions := []
    portals := []
    rules
    tick := 0
    nextId := 1 }

/-- A rule that multiplies velocity, as in the demonstration. -/
def multiplyRule (k : ℚ) : Rule :=
  .body .all (.scaleVelocity k)

/-- The same rule, followed by the speed limiter. -/
def limitedRule (k : ℚ) : Rule :=
  .seq (multiplyRule k) (.body .all .clampVelocity)

/-- Each fixture: a file name, the method and path, and the request. -/
def fixtureRequests : List (String × String × String × Json) :=
  let w := encWorld (speedWorld [])
  let velocity := encProperty .boundedVelocity
  let stationary := encConstraint (.body .speedSquared .eq 0)
  let movesAtFive := encConstraint (.body .speedSquared .eq 25)
  [ ("health", "GET", "/api/health", Json.mkObj []),
    ("theorems", "GET", "/api/theorems", Json.mkObj []),
    ("presets", "GET", "/api/presets", Json.mkObj []),
    ("create", "POST", "/api/universe/create", Json.mkObj [("preset", "cosmos"), ("seed", (42 : Nat))]),
    ("step-unprotected", "POST", "/api/universe/step",
      Json.mkObj [("world", w), ("event", encEvent .reverseGravity), ("mode", "unprotected")]),
    ("step-protected-rejected", "POST", "/api/universe/step",
      Json.mkObj [("world", w), ("event", encEvent (.changeMaxSpeed (-1))), ("mode", "protected")]),
    ("step-protected-repaired", "POST", "/api/universe/step",
      Json.mkObj [("world", w), ("event", encEvent (.addRule (multiplyRule 100))),
        ("mode", "protected")]),
    ("run-frames", "POST", "/api/universe/run",
      Json.mkObj [("world", w), ("steps", (5 : Nat)), ("mode", "protected")]),
    ("validate-rules", "POST", "/api/universe/validate-rules",
      Json.mkObj [("rules", encList encRule [limitedRule 100, multiplyRule 100])]),
    ("consistency-ok", "POST", "/api/universe/check-consistency",
      Json.mkObj [("world", encWorld (speedWorld [limitedRule 100])),
        ("constraints", Json.arr #[movesAtFive])]),
    ("consistency-contradiction", "POST", "/api/universe/check-consistency",
      Json.mkObj [("world", w), ("constraints", Json.arr #[stationary, movesAtFive])]),
    ("consistency-underspecified", "POST", "/api/universe/check-consistency",
      Json.mkObj [("world", encWorld { speedWorld [] with
        portals := [⟨centreBox 1, none, .none⟩],
        laws := { (speedWorld []).laws with pairForce := .div (.const 1) .dist } })]),
    ("verify-proven-clamp", "POST", "/api/universe/verify-property",
      Json.mkObj [("world", encWorld (speedWorld [limitedRule 100])), ("property", velocity)]),
    ("verify-counterexample-multiply", "POST", "/api/universe/verify-property",
      Json.mkObj [("world", encWorld (speedWorld [multiplyRule 100])), ("property", velocity)]),
    ("find-counterexample", "POST", "/api/universe/find-counterexample",
      Json.mkObj [("world", encWorld (speedWorld [multiplyRule 100])), ("property", velocity),
        ("scope", "allowed")]),
    ("check-event", "POST", "/api/universe/check-event",
      Json.mkObj [("world", w), ("event", encEvent (.changeRestitution 5))]),
    ("random-events", "POST", "/api/universe/random-events",
      Json.mkObj [("seed", (7 : Nat)), ("count", (5 : Nat)), ("kind", "safe")]),
    ("audit-laws", "POST", "/api/universe/audit-laws",
      Json.mkObj [("world", encWorld { speedWorld [] with
        laws := { (speedWorld []).laws with
          gravity := Vec3.zero
          reaction := 0
          pairForce := .const 1 } })]) ]

/-- Write every fixture as a file holding its request and response. -/
def writeFixtures (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  for (name, method, path, request) in fixtureRequests do
    let reply := handle method path request.compress
    let entry := Json.mkObj [("method", method), ("path", path), ("request", request),
      ("status", (reply.code : Nat)), ("response", reply.body)]
    IO.FS.writeFile (dir / s!"{name}.json") (entry.pretty ++ "\n")
    IO.println s!"{name}: {reply.code}"

end Paradox.Api

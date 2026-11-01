import Lean.Data.Json
import Paradox.Start

/-!
# The wire format

Rationals travel as strings such as `"49/10"`, so no precision is lost. This layer is tested but not
proved correct. It is listed as trusted in the README.
-/

namespace Paradox.Api

open Lean (Json)

/-- A decoding result: the value, or what was wrong. -/
abbrev Dec := Except String

def field (j : Json) (k : String) : Dec Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error _ => throw s!"missing field '{k}'"

def encRat (q : ℚ) : Json :=
  if q.den = 1 then Json.str (toString q.num) else Json.str s!"{q.num}/{q.den}"

/-- Read a rational from `"49/10"`, `"-3"`, `"0.5"`, or a JSON number. All are read exactly. -/
def decRat : Json → Dec ℚ
  | .str s =>
    match s.splitOn "/", s.splitOn "." with
    | [a, b], _ =>
      match a.toInt?, b.toInt? with
      | some n, some d =>
        if d == 0 then throw s!"zero denominator in '{s}'" else pure ((n : ℚ) / (d : ℚ))
      | _, _ => throw s!"bad number '{s}'"
    | [a], [_] =>
      match a.toInt? with
      | some n => pure (n : ℚ)
      | none => throw s!"bad number '{s}'"
    | _, [w, f] =>
      match w.toInt?, f.toNat? with
      | some wi, some fn =>
        let part : ℚ := (fn : ℚ) / ((10 ^ f.length : Nat) : ℚ)
        pure (if w.startsWith "-" then (wi : ℚ) - part else (wi : ℚ) + part)
      | _, _ => throw s!"bad number '{s}'"
    | _, _ => throw s!"bad number '{s}'"
  | .num n => pure ((n.mantissa : ℚ) / ((10 ^ n.exponent : Nat) : ℚ))
  | _ => throw "expected a number"

def ratField (j : Json) (k : String) : Dec ℚ := do decRat (← field j k)

def natField (j : Json) (k : String) : Dec Nat := do
  match (← field j k).getNat? with
  | .ok n => pure n
  | .error _ => throw s!"'{k}' must be a whole number"

def boolField (j : Json) (k : String) : Dec Bool := do
  match (← field j k).getBool? with
  | .ok b => pure b
  | .error _ => throw s!"'{k}' must be true or false"

def encVec (v : Vec3) : Json :=
  Json.mkObj [("x", encRat v.x), ("y", encRat v.y), ("z", encRat v.z)]

def decVec (j : Json) : Dec Vec3 := do
  return ⟨← ratField j "x", ← ratField j "y", ← ratField j "z"⟩

/-- A rational as a floating-point number, for drawing only. Never a formal value. -/
def approx (q : ℚ) : Json :=
  match Lean.JsonNumber.fromFloat? (Float.ofInt q.num / Float.ofNat q.den) with
  | .inr n => .num n
  | .inl _ => .null

def encBody (b : Body) : Json :=
  Json.mkObj [("id", (b.id : Nat)), ("position", encVec b.position), ("velocity", encVec b.velocity),
    ("mass", encRat b.mass), ("radius", encRat b.radius),
    ("draw", Json.arr #[approx b.position.x, approx b.position.y, approx b.position.z]),
    ("drawVelocity", Json.arr #[approx b.velocity.x, approx b.velocity.y, approx b.velocity.z])]

def decBody (j : Json) : Dec Body := do
  return ⟨← natField j "id", ← decVec (← field j "position"), ← decVec (← field j "velocity"),
    ← ratField j "mass", ← ratField j "radius"⟩

def encBounds (b : Bounds) : Json :=
  Json.mkObj [("minX", encRat b.minX), ("maxX", encRat b.maxX), ("minY", encRat b.minY),
    ("maxY", encRat b.maxY), ("minZ", encRat b.minZ), ("maxZ", encRat b.maxZ)]

def decBounds (j : Json) : Dec Bounds := do
  return ⟨← ratField j "minX", ← ratField j "maxX", ← ratField j "minY", ← ratField j "maxY",
    ← ratField j "minZ", ← ratField j "maxZ"⟩

def encLaws (l : Laws) : Json :=
  Json.mkObj [("gravity", encRat l.gravity), ("pull", encRat l.pull), ("thirdLaw", Json.bool l.thirdLaw),
    ("restitution", encRat l.restitution), ("multiplier", encRat l.multiplier),
    ("limiter", Json.bool l.limiter), ("maxSpeed", encRat l.maxSpeed),
    ("timeStep", encRat l.timeStep), ("grid", (l.grid : Nat))]

def decLaws (j : Json) : Dec Laws := do
  return ⟨← ratField j "gravity", ← ratField j "pull", ← boolField j "thirdLaw",
    ← ratField j "restitution", ← ratField j "multiplier", ← boolField j "limiter",
    ← ratField j "maxSpeed", ← ratField j "timeStep", ← natField j "grid"⟩

def encWorld (w : World) : Json :=
  Json.mkObj [("bodies", Json.arr (w.bodies.map encBody).toArray), ("bounds", encBounds w.bounds),
    ("laws", encLaws w.laws), ("tick", (w.tick : Nat))]

def decWorld (j : Json) : Dec World := do
  let bodies ← (← field j "bodies").getArr?
  return ⟨(← bodies.mapM decBody).toList, ← decBounds (← field j "bounds"),
    ← decLaws (← field j "laws"), ← natField j "tick"⟩

end Paradox.Api

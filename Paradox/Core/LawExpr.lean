import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Sqrt

/-!
# A language for inventing laws of physics

A `LawExpr` is a formula for a force. Users can write any formula from these pieces. Every formula
gives an exact answer for every input: dividing by zero gives zero.
-/

namespace Paradox

/-- A formula. "A" is the body being acted on and "B" is the other body, if there is one. -/
inductive LawExpr where
  | const (q : ℚ)
  | massA
  | massB
  | chargeA
  | chargeB
  /-- The distance between the bodies, squared. -/
  | distSquared
  /-- The distance between the bodies, to within 1/1024. -/
  | dist
  /-- The speed of body A, squared. -/
  | speedSquared
  | add (a b : LawExpr)
  | sub (a b : LawExpr)
  | mul (a b : LawExpr)
  | div (a b : LawExpr)
  | neg (a : LawExpr)
  /-- `a` to the power `n`. Powers above 16 count as 16, which keeps results a sensible size. -/
  | pow (a : LawExpr) (n : Nat)
  deriving DecidableEq, Repr

/-- The values a formula can use. -/
structure LawInputs where
  massA : ℚ
  massB : ℚ
  chargeA : ℚ
  chargeB : ℚ
  distSquared : ℚ
  speedSquared : ℚ

/-- The square root of `q`, rounded down to a multiple of 1/1024. Negative values give zero. -/
def approxSqrt (q : ℚ) : ℚ :=
  if q ≤ 0 then 0 else ((Nat.sqrt ⌊q * 1048576⌋.toNat : Nat) : ℚ) / 1024

/-- The value of a formula for the given inputs. -/
def LawExpr.eval (i : LawInputs) : LawExpr → ℚ
  | .const q => q
  | .massA => i.massA
  | .massB => i.massB
  | .chargeA => i.chargeA
  | .chargeB => i.chargeB
  | .distSquared => i.distSquared
  | .dist => approxSqrt i.distSquared
  | .speedSquared => i.speedSquared
  | .add a b => a.eval i + b.eval i
  | .sub a b => a.eval i - b.eval i
  | .mul a b => a.eval i * b.eval i
  | .div a b => a.eval i / b.eval i
  | .neg a => -(a.eval i)
  | .pow a n => (a.eval i) ^ (min n 16)

end Paradox

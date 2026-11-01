import Paradox.Invariants.Property
import Paradox.Rules.Syntax

/-!
# Checking rules without running them

These checks read a rule and answer "this is safe" or "I cannot tell". `Verification/RuleSoundness`
proves that "safe" is always correct. "I cannot tell" says nothing: such a rule may still be safe.
-/

namespace Paradox

/-- What a formula's sign is known to be, given positive mass. The first value means "always
positive" and the second means "never negative". -/
def LawExpr.sign : LawExpr → Bool × Bool
  | .const q => (decide (0 < q), decide (0 ≤ q))
  | .massA => (true, true)
  | .distSquared => (false, true)
  | .dist => (false, true)
  | .speedSquared => (false, true)
  | .add a b =>
    let sa := a.sign
    let sb := b.sign
    ((sa.1 && sb.2) || (sa.2 && sb.1), sa.2 && sb.2)
  | .mul a b =>
    let sa := a.sign
    let sb := b.sign
    (sa.1 && sb.1, sa.2 && sb.2)
  | .div a b =>
    let sa := a.sign
    let sb := b.sign
    (sa.1 && sb.1, sa.2 && sb.2)
  | .pow a n =>
    let sa := a.sign
    (sa.1 || n == 0, sa.2 || n == 0)
  | _ => (false, false)

/-- The rule cannot make the environment unsafe. -/
def Rule.envSafe : Rule → Bool
  | .world (.setMaxSpeed v) => decide (0 < v)
  | .world (.setMassRate r) => decide (0 < r)
  | .seq a b => a.envSafe && b.envSafe
  | .when _ r => r.envSafe
  | _ => true

/-- The body action cannot turn the property from true to false. -/
def BodyAction.keeps : Property → BodyAction → Bool
  | .positiveMass, .scaleMass k => decide (0 < k)
  | .positiveMass, .setMassFormula f => f.sign.1
  | .positiveMass, _ => true
  | .boundedPosition, .translate _ => false
  | .boundedPosition, _ => true
  | .boundedVelocity, .applyForce _ => false
  | .boundedVelocity, .scaleVelocity k => decide (|k| ≤ 1)
  | .boundedVelocity, _ => true
  | .safeEnvironment, _ => true
  | .uniqueIds, _ => true

/-- The world action cannot turn the property from true to false. -/
def WorldAction.keeps : Property → WorldAction → Bool
  | .boundedVelocity, .setMaxSpeed _ => false
  | .safeEnvironment, .setMaxSpeed v => decide (0 < v)
  | .safeEnvironment, .setMassRate r => decide (0 < r)
  | _, _ => true

/-- The rule makes the property true whatever it was before, in a safe environment. -/
def Rule.establishes (p : Property) : Rule → Bool
  | .body .all .clampVelocity => p == .boundedVelocity
  | .body .all .clampPosition => p == .boundedPosition
  | .seq a b => a.envSafe && b.establishes p
  | _ => false

/-- The rule cannot turn the property from true to false, in a safe environment. -/
def Rule.keeps (p : Property) : Rule → Bool
  | .skip => true
  | .body _ a => a.keeps p
  | .world a => a.keeps p
  | .destroy _ => true
  | .create _ => true
  | .seq a b => a.envSafe && ((a.keeps p && b.keeps p) || b.establishes p)
  | .when _ r => r.keeps p

/-- The rule is safe for every guarantee. Only these rules are allowed in a protected universe. -/
def Rule.certified (r : Rule) : Bool :=
  r.envSafe && Property.all.all (fun p => r.keeps p)

/-- Try to make a rule safe by bringing velocity and position back in range after it runs. -/
def Rule.repair (r : Rule) : Option Rule :=
  let repaired := Rule.seq (.seq r (.body .all .clampVelocity)) (.body .all .clampPosition)
  if repaired.certified then some repaired else none

end Paradox

import Paradox.Verification.Preservation

/-!
# Layer B: transition consistency

Are the rules defined well enough to say what happens next? `step` always gives an answer, because
Lean functions are total. But some answers are only conventions: dividing by zero gives zero, and a
portal with no exit leaves a body in place. These checks report when a universe relies on one.
They also report when rules disagree about the result depending on the order they run in.
-/

namespace Paradox

/-! ## Formulas with no defined value -/

/-- The value of a formula, or `none` if it divides by zero. -/
def LawExpr.evalChecked (i : LawInputs) : LawExpr → Option ℚ
  | .const q => some q
  | .massA => some i.massA
  | .massB => some i.massB
  | .chargeA => some i.chargeA
  | .chargeB => some i.chargeB
  | .distSquared => some i.distSquared
  | .dist => some (approxSqrt i.distSquared)
  | .speedSquared => some i.speedSquared
  | .add a b => do return (← a.evalChecked i) + (← b.evalChecked i)
  | .sub a b => do return (← a.evalChecked i) - (← b.evalChecked i)
  | .mul a b => do return (← a.evalChecked i) * (← b.evalChecked i)
  | .div a b => do
    let d ← b.evalChecked i
    if d = 0 then none else return (← a.evalChecked i) / d
  | .neg a => do return -(← a.evalChecked i)
  | .pow a n => do return (← a.evalChecked i) ^ (min n 16)

/-- Every division in the formula is by something known to be positive. -/
def LawExpr.divisionsSafe : LawExpr → Bool
  | .add a b | .sub a b | .mul a b => a.divisionsSafe && b.divisionsSafe
  | .div a b => a.divisionsSafe && b.divisionsSafe && b.sign.1
  | .neg a | .pow a _ => a.divisionsSafe
  | _ => true

/-- **A formula that passes the check always has a defined value**, and it equals `eval`. -/
theorem LawExpr.divisionsSafe_sound (i : LawInputs) (hm : 0 < i.massA) (hd : 0 ≤ i.distSquared)
    (hs : 0 ≤ i.speedSquared) (e : LawExpr) (h : e.divisionsSafe = true) :
    e.evalChecked i = some (e.eval i) := by
  induction e with
  | add a b iha ihb =>
    simp only [divisionsSafe, Bool.and_eq_true] at h
    simp [evalChecked, eval, iha h.1, ihb h.2]
  | sub a b iha ihb =>
    simp only [divisionsSafe, Bool.and_eq_true] at h
    simp [evalChecked, eval, iha h.1, ihb h.2]
  | mul a b iha ihb =>
    simp only [divisionsSafe, Bool.and_eq_true] at h
    simp [evalChecked, eval, iha h.1, ihb h.2]
  | div a b iha ihb =>
    simp only [divisionsSafe, Bool.and_eq_true] at h
    have hpos := (LawExpr.sign_sound i hm hd hs b).1 h.2
    simp [evalChecked, eval, iha h.1.1, ihb h.1.2, hpos.ne']
  | neg a iha => simp [evalChecked, eval, iha h]
  | pow a n iha => simp [evalChecked, eval, iha h]
  | _ => rfl

/-- Inputs likely to expose a formula with no defined value. -/
def probeInputs : List LawInputs :=
  [ ⟨1, 1, 0, 0, 0, 0⟩, ⟨1, 1, 1, 1, 1, 0⟩, ⟨1, 1, 0, 0, 1, 1⟩, ⟨1, 1, 1, -1, 4, 1⟩ ]

/-- What is known about a formula's definedness. -/
inductive FormulaStatus where
  /-- Proved defined for every input with positive mass. -/
  | defined
  /-- These inputs give no defined value. -/
  | undefinedAt (i : Nat)
  /-- The check could not tell. -/
  | unknown
  deriving DecidableEq, Repr

/-- Check a formula: a proof of definedness, or inputs where it has no value, or unknown. -/
def LawExpr.definedness (e : LawExpr) : FormulaStatus :=
  if e.divisionsSafe then .defined
  else match probeInputs.findIdx? (fun i => (e.evalChecked i).isNone) with
    | some n => .undefinedAt n
    | none => .unknown

/-! ## Names and destinations -/

/-- The region names a condition uses. -/
def BodyCond.regionNames : BodyCond → List String
  | .inRegion name => [name]
  | .not c => c.regionNames
  | _ => []

/-- The region names a rule uses. -/
def Rule.regionNames : Rule → List String
  | .body c _ => c.regionNames
  | .destroy c => c.regionNames
  | .seq a b => a.regionNames ++ b.regionNames
  | .when _ r => r.regionNames
  | _ => []

/-- A region a rule names but the world does not have. -/
def missingRegions (w : World) : List String :=
  (w.rules.flatMap Rule.regionNames).filter fun name =>
    !(w.regions.any fun r => r.name == name)

/-- The portals with no destination. -/
def portalsWithoutExit (w : World) : List Portal :=
  w.portals.filter fun p => p.exit.isNone

/-! ## Rules and order -/

/-- Two world actions that change different laws. -/
def WorldAction.independent : WorldAction → WorldAction → Bool
  | .setGravity _, .setGravity _ | .setGravity _, .reverseGravity
  | .reverseGravity, .setGravity _ | .reverseGravity, .reverseGravity => false
  | .setMaxSpeed _, .setMaxSpeed _ => false
  | .setPairForce _, .setPairForce _ => false
  | .setReaction _, .setReaction _ => false
  | .setMassRate _, .setMassRate _ => false
  | _, _ => true

/-- World actions on different laws can run in either order with the same result. -/
theorem WorldAction.independent_commute (a b : WorldAction) (h : a.independent b = true)
    (prev w : World) :
    (Rule.world b).eval prev ((Rule.world a).eval prev w) =
      (Rule.world a).eval prev ((Rule.world b).eval prev w) := by
  cases a <;> cases b <;> first | rfl | simp [WorldAction.independent] at h

/-- What is known about two rules running in either order. -/
inductive OrderStatus where
  /-- Proved to give the same result in either order, in every world. -/
  | independent
  /-- In the checked world, the two orders give different results. -/
  | conflict
  /-- In the checked world the orders agree, but they may differ in other worlds. -/
  | agreesHere
  deriving DecidableEq, Repr

/-- Compare two rules in the world `w`. -/
def orderStatus (w : World) (a b : Rule) : OrderStatus :=
  match a, b with
  | .world x, .world y =>
    if x.independent y then .independent
    else if b.eval w (a.eval w w) ≠ a.eval w (b.eval w w) then .conflict else .agreesHere
  | _, _ =>
    if b.eval w (a.eval w w) ≠ a.eval w (b.eval w w) then .conflict else .agreesHere

/-- **A reported conflict is real**: this world has two different next states for this pair. -/
theorem orderStatus_conflict {w : World} {a b : Rule} (h : orderStatus w a b = .conflict) :
    b.eval w (a.eval w w) ≠ a.eval w (b.eval w w) := by
  unfold orderStatus at h
  split at h
  · split at h
    · simp at h
    · split at h
      · assumption
      · simp at h
  · split at h
    · assumption
    · simp at h

/-- **A reported independence is real**: the order never matters. -/
theorem orderStatus_independent {w : World} {a b : Rule} (h : orderStatus w a b = .independent) :
    ∃ x y, a = .world x ∧ b = .world y ∧ ∀ prev v,
      b.eval prev (a.eval prev v) = a.eval prev (b.eval prev v) := by
  unfold orderStatus at h
  split at h
  · rename_i x y
    split at h
    next hi => exact ⟨x, y, rfl, rfl, fun prev v => WorldAction.independent_commute x y hi prev v⟩
    next =>
      split at h <;> simp at h
  · split at h <;> simp at h

/-- All pairs of rules that conflict in this world. -/
def ruleConflicts (w : World) : List (Rule × Rule) :=
  let indexed := w.rules.zipIdx
  (indexed.flatMap fun p => indexed.filterMap fun q =>
    if p.2 < q.2 && orderStatus w p.1 q.1 == .conflict then some (p.1, q.1) else none)

/-- The result of the transition consistency check. -/
structure TransitionReport where
  missingRegions : List String
  portalsWithoutExit : List Portal
  undefinedFormulas : List (String × FormulaStatus)
  unknownFormulas : List String
  conflicts : List (Rule × Rule)
  deriving Repr

/-- Each formula law with its name. -/
def namedFormulas (l : PhysicsLaws) : List (String × LawExpr) :=
  [("pairForce", l.pairForce), ("drag", l.drag), ("central", l.central)]

/-- Check how well defined the world's transitions are. -/
def checkTransitions (w : World) : TransitionReport :=
  let statuses := (namedFormulas w.laws).map fun p => (p.1, p.2.definedness)
  { missingRegions := missingRegions w
    portalsWithoutExit := portalsWithoutExit w
    undefinedFormulas := statuses.filter fun p =>
      match p.2 with
      | .undefinedAt _ => true
      | _ => false
    unknownFormulas := (statuses.filter fun p => p.2 == .unknown).map Prod.fst
    conflicts := ruleConflicts w }

end Paradox

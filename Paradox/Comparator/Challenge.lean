import Paradox.Rules.Random
import Paradox.Verification.LawAudit
import Paradox.Consistency.Transitions

/-!
# The statements PARADOX stands behind

This file is for reading. It lists the main results, with no proofs. `Solution.lean` proves these
exact statements, and `lake comparator` checks that independently of the rest of the project. See
`comparator.json`.

Do not import this file: every `sorry` here is deliberate and is replaced in `Solution.lean`.
-/

namespace Paradox.Comparator

open Paradox

/-- A guarantee survives any finite list of permitted events. -/
theorem run_inv (p : Property) (w : World) (events : List EnvironmentEvent)
    (hw : Inv p w) (htrace : Engine.AllowedTrace step Allowed w events) : Inv p (run w events) :=
  sorry

/-- All guarantees survive any finite list of permitted events. -/
theorem guaranteed_run (w : World) (events : List EnvironmentEvent) (hw : Guaranteed w)
    (htrace : Engine.AllowedTrace step Allowed w events) : Guaranteed (run w events) :=
  sorry

/-- A guarantee holds whatever order the rules run in. -/
theorem next_inv (p : Property) (e : EnvironmentEvent) (w : World) (ha : Allowed w e) (hw : Inv p w)
    {w' : World} (hn : Next e w w') : Inv p w' :=
  sorry

/-- In protected mode, no list of events can break a guarantee. -/
theorem protectedRun_safe (p : Property) (w : World) (events : List EnvironmentEvent) (h : Inv p w) :
    Inv p (protectedRun w events) :=
  sorry

/-- Any constraint can be enforced by refusing changes that would break it. -/
theorem enforcedRun_holds (cs : List Constraint) (w : World) (events : List EnvironmentEvent)
    (h : ∀ c ∈ cs, c.holds w) : ∀ c ∈ cs, c.holds (enforcedRun cs w events) :=
  sorry

/-- Every seeded random experiment keeps every guarantee. -/
theorem random_chaos_safe (seed n : Nat) (w : World) (h : Guaranteed w) :
    Guaranteed (run w (safeEvents seed n)) :=
  sorry

/-- The universe from any seed starts with every guarantee true. -/
theorem generateWorld_guaranteed (seed : Nat) : Guaranteed (generateWorld seed) :=
  sorry

/-- If the rule checker clears a rule, the rule keeps the guarantee. -/
theorem keeps_sound (prev : World) (p : Property) (r : Rule) (w : World) (hk : r.keeps p = true)
    (he : SafeEnvironment w) (hp : p.holds w) : p.holds (r.eval prev w) :=
  sorry

/-- A checked counterexample really happens and really breaks the claim. -/
theorem checkTrace_sound {scope : EventScope} {claim : Claim} {t : WorldTrace}
    (h : checkTrace scope claim t = true) :
    InScope scope t.initial t.events ∧ ¬ claim.holds t.initial (run t.initial t.events) :=
  sorry

/-- A `proven` verdict from the API is correct. -/
theorem verifyProperty_proven {limits : SearchLimits} {p : Property} {w : World}
    (h : (verifyProperty limits p w).status = .proven) (events : List EnvironmentEvent)
    (htrace : Engine.AllowedTrace step Allowed w events) : p.holds (run w events) :=
  sorry

/-- A counterexample in a verdict has passed the checker. -/
theorem verifyProperty_counterexample {limits : SearchLimits} {p : Property} {w : World} {t : WorldTrace}
    (h : (verifyProperty limits p w).counterexample = some t) :
    checkTrace .allowed (.property p) t = true :=
  sorry

/-- With Newton's third law on, every invented force law keeps total momentum. -/
theorem pairForces_conserve_momentum (laws : PhysicsLaws) (hr : laws.reaction = 1) (c : Vec3) (l : List Body)
    (hl : ∀ x ∈ l, 0 < x.mass) :
    totalMomentum c (pairAll (forcePair laws) l) = totalMomentum c l :=
  sorry

/-- Forces between bodies and momentum-keeping collisions never change total momentum. -/
theorem interaction_conserves_momentum (laws : PhysicsLaws) (hr : laws.reaction = 1)
    (hm : laws.collisions.KeepsMomentum) (c : Vec3) (nextId : Nat) (l : List Body)
    (hl : ∀ x ∈ l, 0 < x.mass) :
    totalMomentum c (collisionStage laws nextId (pairAll (forcePair laws) l)).1 =
      totalMomentum c l :=
  sorry

/-- With no forces, total kinetic energy can only stay level or fall. -/
theorem idleRun_energy_le (n : Nat) (w : World) (hrules : w.rules = []) (hf : w.laws.NoForces)
    (hc : w.laws.collisions = .none ∨ w.laws.collisions = .bounce)
    (he : SafeEnvironment w) (hpos : PositiveMass w) (hr1 : w.laws.massRate ≤ 1) :
    totalEnergy (run w (idleEvents n)).bodies ≤ totalEnergy w.bodies :=
  sorry

/-- Total mass stays the same as time passes, under the stated laws. -/
theorem idleRun_conserves_mass (n : Nat) (w : World) (hrules : w.rules = [])
    (hr : w.laws.massRate = 1) (hm : w.laws.collisions.NoCreation) (hpos : PositiveMass w) :
    totalMass (run w (idleEvents n)).bodies = totalMass w.bodies :=
  sorry

/-- A returned example universe really meets every constraint. -/
theorem checkConstraints_satisfiable {base : World} {cs : List Constraint} {w : World}
    (h : checkConstraints base cs = .satisfiable w) : Valid base cs w :=
  sorry

/-- A reported contradiction means no valid universe exists. -/
theorem checkConstraints_contradiction {base : World} {cs : List Constraint} {a b : Constraint}
    (h : checkConstraints base cs = .contradiction a b) : ¬ ∃ w, Valid base cs w :=
  sorry

/-- A formula that passes the division check has a defined value. -/
theorem divisionsSafe_sound (i : LawInputs) (hm : 0 < i.massA) (hd : 0 ≤ i.distSquared)
    (hs : 0 ≤ i.speedSquared) (e : LawExpr) (h : e.divisionsSafe = true) :
    e.evalChecked i = some (e.eval i) :=
  sorry

/-- A reported rule conflict is real. -/
theorem orderStatus_conflict {w : World} {a b : Rule} (h : orderStatus w a b = .conflict) :
    b.eval w (a.eval w w) ≠ a.eval w (b.eval w w) :=
  sorry

end Paradox.Comparator

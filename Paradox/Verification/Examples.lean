import Paradox.Rules.Random
import Paradox.Verification.LawAudit
import Paradox.Consistency.Transitions

/-!
# Sanity checks on the theorems

These guard against theorems that are true for uninteresting reasons:

* The main theorems are applied to concrete inputs with every hypothesis proved, so their hypotheses
  can be met.
* Each guarantee is shown to reject a bad world, so none is trivially true.
* The `#guard`s pin exact results, so a `tick` that did nothing would fail the build.
-/

namespace Paradox

open Engine

/-! ## Test worlds -/

/-- A body for tests. -/
def testBody (id : Nat) (p v : Vec3) (m : ℚ := 1) : Body :=
  { id, shape := .sphere (1 / 2), position := p, velocity := v, mass := m, charge := 0 }

/-- Exact test laws: no rounding, no collisions. -/
def testLaws : PhysicsLaws :=
  { defaultLaws with
    timeStep := 1 / 10
    maxSpeed := 20
    maxAcceleration := 30
    grid := 0
    collisions := .none
    restitution := 1 / 2 }

/-- A test world with these bodies. -/
def testWorld (bodies : List Body) (laws : PhysicsLaws := testLaws) : World :=
  { bodies, bounds := defaultBounds, laws, regions := [], portals := [], rules := [], tick := 0,
    nextId := 100 }

/-- One moving sphere. -/
def oneBody : World := testWorld [testBody 0 ⟨0, 5, 0⟩ ⟨1, 0, 0⟩]

/-! ## The hypotheses can be met -/

/-- An event sequence that strengthens, reverses and removes gravity and changes the force law. -/
def stressEvents : List EnvironmentEvent :=
  [.changeGravity ⟨0, -100, 0⟩, .reverseGravity, .changeMaxSpeed (1 / 2), .disableGravity,
   .setPairForce (.div (.const 1) .dist), .setReaction 0, .setTopology .torus, .idle]

/-- `guaranteed_run` on a concrete start and event list, with every hypothesis proved. -/
example : Guaranteed (run (generateWorld 42) stressEvents) :=
  guaranteed_run _ _ (generateWorld_guaranteed 42)
    ⟨trivial, trivial, (by show (0 : ℚ) < 1 / 2; norm_num), trivial, trivial, trivial, trivial,
     trivial, trivial⟩

/-- `protectedRun_guaranteed` on events that include ones protected mode must refuse. -/
example : Guaranteed (protectedRun (generateWorld 7)
    [.changeMaxSpeed (-1), .changeRestitution 5, .addRule (.body .all (.scaleVelocity 1000))]) :=
  protectedRun_guaranteed _ _ (generateWorld_guaranteed 7)

/-- `random_chaos_safe` for a concrete seed. -/
example : Guaranteed (run (generateWorld 1) (safeEvents 2 1000)) :=
  random_chaos_safe 2 1000 _ (generateWorld_guaranteed 1)

/-- `next_inv` with a rule order chosen. -/
example (p : Property) :
    Inv p (evalRules (generateWorld 3) [] (tick (applyEvent (generateWorld 3) .idle))) :=
  next_inv p .idle _ trivial (generateWorld_guaranteed 3 p) ⟨[], by simp [applyEvent, generateWorld], rfl⟩

/-- `negative_maxSpeed_violates`: the velocity theorem cannot be widened to every event. -/
theorem negative_speed_breaks_oneBody :
    ¬ BoundedVelocity (tick (applyEvent oneBody (.changeMaxSpeed (-1)))) := by
  refine negative_maxSpeed_violates (by norm_num) ?_
  simp [tick, applyEvent, withLaws, oneBody, testWorld, collisionStage, testLaws, applyForces,
    pairAll, pairOne]

/-! ## The guarantees reject bad worlds -/

example : ¬ PositiveMass (testWorld [testBody 0 ⟨0, 0, 0⟩ Vec3.zero 0]) := by
  norm_num [PositiveMass, testWorld, testBody]

example : ¬ BoundedPosition (testWorld [testBody 0 ⟨10, 0, 0⟩ Vec3.zero]) := by
  norm_num [BoundedPosition, Bounds.Contains, Bounds.inset, testWorld, testBody, defaultBounds,
    Body.extent, Shape.extent]

example : ¬ BoundedVelocity (testWorld [testBody 0 ⟨0, 0, 0⟩ ⟨21, 0, 0⟩]) := by
  norm_num [BoundedVelocity, Vec3.WithinAbs, testWorld, testBody, testLaws, defaultLaws]

example : ¬ UniqueIds (testWorld [testBody 0 ⟨0, 0, 0⟩ Vec3.zero, testBody 0 ⟨1, 0, 0⟩ Vec3.zero]) := by
  simp [UniqueIds, testWorld, testBody]

example : ¬ SafeEnvironment (testWorld [] { testLaws with restitution := 5 }) := by
  norm_num [SafeEnvironment, testWorld]

/-! ## Exact physics -/

/-- The first body's position and velocity after a step. -/
def firstMotion (w : World) : Option (Vec3 × Vec3) :=
  w.bodies.head?.map fun b => (b.position, b.velocity)

-- Falling under gravity: v = (1, -1, 0), p = (1/10, 49/10, 0).
#guard firstMotion (step oneBody .idle) == some (⟨1 / 10, 49 / 10, 0⟩, ⟨1, -1, 0⟩)
-- Reversing gravity acts in the same step.
#guard firstMotion (step oneBody .reverseGravity) == some (⟨1 / 10, 51 / 10, 0⟩, ⟨1, 1, 0⟩)
-- Lowering the speed limit acts in the same step.
#guard (firstMotion (step oneBody (.changeMaxSpeed (1 / 2)))).map (·.2) == some ⟨1 / 2, -1 / 2, 0⟩
-- Time passes.
#guard (step oneBody .idle).tick == 1

/-- A body about to hit the right wall of a box. -/
def nearWall (laws : PhysicsLaws) : World :=
  testWorld [testBody 0 ⟨19 / 2, 0, 0⟩ ⟨10, 0, 0⟩] { laws with gravity := Vec3.zero }

-- In a box, a body stops at the wall and bounces at half speed.
#guard firstMotion (step (nearWall testLaws) .idle) == some (⟨19 / 2, 0, 0⟩, ⟨-5, 0, 0⟩)
-- In a torus, it comes back on the far side at the same speed. The room is 19 wide.
#guard firstMotion (step (nearWall { testLaws with topology := .torus }) .idle) ==
  some (⟨-17 / 2, 0, 0⟩, ⟨10, 0, 0⟩)

/-- A world with a portal covering the point a body is about to reach. -/
def portalWorld (effect : PortalEffect) (exit : Option Vec3) : World :=
  { testWorld [testBody 0 ⟨0, 0, 0⟩ ⟨10, 0, 0⟩] { testLaws with gravity := Vec3.zero } with
    portals := [⟨⟨0, 2, -1, 1, -1, 1⟩, exit, effect⟩] }

-- A portal moves the body and multiplies its velocity.
#guard firstMotion (step (portalWorld (.scale 2) (some ⟨5, 5, 5⟩)) .idle) ==
  some (⟨5, 5, 5⟩, ⟨20, 0, 0⟩)
-- A portal with no exit leaves the body where it landed. Its effect still applies.
#guard firstMotion (step (portalWorld .reverse none) .idle) == some (⟨1, 0, 0⟩, ⟨-10, 0, 0⟩)
-- A portal that multiplies by more than 1 can break the speed limit: its counterexample is real.
#guard !decide (BoundedVelocity (step (portalWorld (.scale 3) (some ⟨5, 5, 5⟩)) .idle))

-- Time runs at half speed inside a region.
#guard firstMotion (step { testWorld [testBody 0 ⟨0, 0, 0⟩ ⟨2, 0, 0⟩]
    { testLaws with gravity := Vec3.zero } with
    regions := [⟨"slow", "blue", defaultBounds, 1 / 2⟩] } .idle) == some (⟨1 / 10, 0, 0⟩, ⟨2, 0, 0⟩)

-- Mass decays at the mass rate.
#guard ((step (testWorld [testBody 0 ⟨0, 0, 0⟩ Vec3.zero 2]
    { testLaws with massRate := 1 / 2 }) .idle).bodies.head?.map (·.mass)) == some 1

-- The grid rounds toward zero, in both directions.
#guard snap 8 (3 / 16) == 1 / 8
#guard snap 8 (-3 / 16) == -1 / 8
#guard snap 0 (3 / 16) == 3 / 16

/-- Two touching bodies moving toward each other. -/
def headOn (mode : CollisionMode) (e : ℚ := 1) : World :=
  testWorld [testBody 0 ⟨0, 0, 0⟩ ⟨1, 0, 0⟩, testBody 1 ⟨1 / 2, 0, 0⟩ ⟨-1, 0, 0⟩]
    { testLaws with gravity := Vec3.zero, collisions := mode, restitution := e }

-- Equal masses at restitution 1 swap velocities.
#guard (step (headOn .bounce) .idle).bodies.map (·.velocity) == [⟨-1, 0, 0⟩, ⟨1, 0, 0⟩]
-- Merging keeps total mass and leaves one body.
#guard ((step (headOn .merge) .idle).bodies.map (·.mass)) == [2]
-- Spawning adds one body, with a new id.
#guard (step (headOn .spawn) .idle).bodies.map (·.id) == [0, 1, 100]
#guard (step (headOn .spawn) .idle).nextId == 101
-- Exchanging velocity works at any restitution.
#guard (step (headOn .exchangeVelocity 0) .idle).bodies.map (·.velocity) == [⟨-1, 0, 0⟩, ⟨1, 0, 0⟩]

/-! ## Invented force laws -/

/-- A deliberately strange law: force depends on mass, charge, speed and distance. -/
def strangeLaw : LawExpr :=
  .div (.add (.mul .massA .massB) (.mul .chargeA .speedSquared)) (.add (.const 1) .dist)

/-- Three bodies far apart, under the strange law, with this reaction factor. -/
def strangeWorld (r : ℚ) : World :=
  testWorld [testBody 0 ⟨0, 0, 0⟩ ⟨1, 2, 3⟩ 2, testBody 1 ⟨4, 0, 0⟩ ⟨-1, 0, 1⟩ 3,
             testBody 2 ⟨0, 5, 1⟩ ⟨0, 0, 0⟩ 5]
    { testLaws with gravity := Vec3.zero, pairForce := strangeLaw, reaction := r }

/-- Total momentum along x after the force stage only. -/
def momentumAfterForces (w : World) : ℚ :=
  totalMomentum ⟨1, 0, 0⟩ (pairAll (forcePair w.laws) w.bodies)

-- With the third law on, the theorem's prediction shows up in exact arithmetic.
#guard momentumAfterForces (strangeWorld 1) == totalMomentum ⟨1, 0, 0⟩ (strangeWorld 1).bodies
-- With it off, momentum changes.
#guard momentumAfterForces (strangeWorld 0) != totalMomentum ⟨1, 0, 0⟩ (strangeWorld 0).bodies

/-! ## The rule checker -/

/-- A rule that multiplies velocity. -/
def scaleRule (k : ℚ) : Rule := .body .all (.scaleVelocity k)

#guard !(scaleRule 1000).keeps .boundedVelocity
#guard (scaleRule (1 / 2)).keeps .boundedVelocity
#guard (Rule.seq (scaleRule 1000) (.body .all .clampVelocity)).keeps .boundedVelocity
#guard (scaleRule 1000).keeps .positiveMass
-- The speed limiter only establishes the bound if it reaches every body.
#guard !(Rule.seq (scaleRule 1000) (.body (.speedAbove 5) .clampVelocity)).keeps .boundedVelocity
-- Objects that get heavier as they move faster keep positive mass. That is proved, not assumed.
#guard (Rule.body .all (.setMassFormula (.add .massA (.mul (.const 1) .speedSquared)))).keeps .positiveMass
-- A formula that could reach zero or below is not cleared.
#guard !(Rule.body .all (.setMassFormula (.sub .massA .speedSquared))).keeps .positiveMass
-- Repair works when clamping helps and refuses when it cannot.
#guard (scaleRule 1000).repair.isSome
#guard (Rule.body .all (.scaleMass (-1))).repair.isNone
#guard (Rule.world (.setMaxSpeed (-1))).repair.isNone
-- `create` is safe because it checks validity when it runs.
#guard (Rule.create (testBody 0 ⟨0, 0, 0⟩ ⟨100, 0, 0⟩)).certified

/-- The body that a create rule makes when it can, and the world when it cannot. -/
def createdCount (t : Body) : Nat :=
  ((Rule.create t).eval oneBody oneBody).bodies.length

#guard createdCount (testBody 0 ⟨0, 0, 0⟩ Vec3.zero) == 2
#guard createdCount (testBody 0 ⟨0, 0, 0⟩ ⟨100, 0, 0⟩) == 1
#guard createdCount (testBody 0 ⟨0, 0, 0⟩ Vec3.zero 0) == 1

/-! ## Layer A: rule consistency -/

/-- The contradiction the spec gives as an example. -/
def stationaryAndMoving : List Constraint :=
  [.body .speedSquared .eq 0, .body .speedSquared .eq 25]

/-- Whether the check found a contradiction. -/
def RuleCheck.isContradiction : RuleCheck → Bool
  | .contradiction _ _ => true
  | _ => false

/-- Whether the check found a witness. -/
def RuleCheck.isSatisfiable : RuleCheck → Bool
  | .satisfiable _ => true
  | _ => false

#guard (checkConstraints oneBody stationaryAndMoving).isContradiction
-- A rule against the built-in positive mass is a contradiction.
#guard (checkConstraints oneBody [.body .mass .lt 0]).isContradiction
-- A rule against the speed limit is a contradiction.
#guard (checkConstraints oneBody [.body .velocityX .ge 21]).isContradiction
-- Strict limits at the same value conflict; non-strict ones do not.
#guard (checkConstraints oneBody [.body .charge .gt 1, .body .charge .le 1]).isContradiction
#guard (checkConstraints oneBody [.body .charge .ge 1, .body .charge .le 1]).isSatisfiable
-- An empty universe does not count, so "no objects" is a contradiction.
#guard (checkConstraints oneBody [.population .eq 0]).isContradiction
-- A speed constraint gets a real witness.
#guard (checkConstraints oneBody [.body .speedSquared .eq 25]).isSatisfiable
#guard (checkConstraints oneBody [.population .eq 3, .body .mass .eq 7]).isSatisfiable
-- This is possible (speed² 2 from x = y = 1) but the check does not find it, and says so honestly.
#guard match checkConstraints oneBody [.body .speedSquared .eq 2] with
  | .unknown => true
  | _ => false

/-! ## Layer B: transition consistency -/

-- Dividing by distance has no value when two bodies are at the same point.
#guard (LawExpr.div (.const 1) .dist).definedness == .undefinedAt 0
#guard (LawExpr.div (.const 1) (.add (.const 1) .dist)).definedness == .defined
-- A division the check cannot clear, and the probes do not expose, stays unknown.
#guard (LawExpr.div (.const 1) .massB).definedness == .unknown

#guard !(checkTransitions (portalWorld .none none)).portalsWithoutExit.isEmpty
#guard (checkTransitions (portalWorld .none (some ⟨0, 0, 0⟩))).portalsWithoutExit.isEmpty
#guard (checkTransitions { oneBody with rules := [.body (.inRegion "red") .reverseVelocity] }).missingRegions == ["red"]
#guard (checkTransitions { oneBody with
    rules := [.body (.inRegion "red") .reverseVelocity]
    regions := [⟨"red", "red", defaultBounds, 1⟩] }).missingRegions.isEmpty

-- Two rules setting gravity to different values conflict.
#guard orderStatus oneBody (.world (.setGravity ⟨1, 0, 0⟩)) (.world (.setGravity ⟨2, 0, 0⟩)) == .conflict
-- Setting different laws never conflicts, proved for every world.
#guard orderStatus oneBody (.world (.setGravity ⟨1, 0, 0⟩)) (.world (.setMaxSpeed 2)) == .independent
-- Two equal rules agree here, but that is not called independence.
#guard orderStatus oneBody (.world (.setGravity ⟨1, 0, 0⟩)) (.world (.setGravity ⟨1, 0, 0⟩)) == .agreesHere

/-! ## Layer C: verdicts and counterexamples -/

/-- The spec's first demonstration: speed limit 10 and a rule. -/
def speedDemo (r : Rule) : World :=
  { testWorld [testBody 0 ⟨0, 0, 0⟩ ⟨1, 0, 0⟩] { testLaws with maxSpeed := 10, gravity := ⟨0, 2, 0⟩ }
    with rules := [r] }

/-- The verdict status for the velocity guarantee. -/
def velocityStatus (r : Rule) : Status :=
  (verifyProperty {} .boundedVelocity (speedDemo r)).status

#guard velocityStatus (.seq (scaleRule 100) (.body .all .clampVelocity)) == .proven
#guard velocityStatus (scaleRule 100) == .counterexample

/-- The counterexample for the ×100 rule. -/
def speedCounterexample : Option WorldTrace :=
  searchCounterexample {} .allowed (.property .boundedVelocity) (speedDemo (scaleRule 100))

#guard speedCounterexample.isSome
#guard speedCounterexample.any fun t => checkTrace .allowed (.property .boundedVelocity) t
-- A tampered trace fails: the claimed final state is not what the model produces.
#guard speedCounterexample.any fun t =>
  !checkTrace .any (.property .boundedVelocity)
    { t with states := t.states.map fun s => { s with tick := s.tick + 1 } }
-- A trace of a claim that holds fails too, even if the replay is right.
#guard speedCounterexample.any fun t => !checkTrace .any (.property .positiveMass) t

-- Failure to prove is not failure. With no events that could break it and no search budget,
-- the answer is unknown, not counterexample.
#guard (verifyClaim { depth := 0, idleSteps := 0 } (.constraint (.population .le 1)) oneBody).status == .unknown
-- The search finds a permitted spawn that breaks the population limit.
#guard (verifyClaim {} (.constraint (.population .le 1)) oneBody).status == .counterexample

-- A rule that is safe but cannot be cleared gets unknown. Events that break the rules on purpose
-- do not count against it: those are only searched when asked for.
#guard (verifyProperty {} .boundedPosition { oneBody with
    rules := [.body (.speedAbove 100000) (.translate ⟨1, 0, 0⟩)] }).status == .unknown
#guard (searchCounterexample {} .any (.property .boundedPosition) { oneBody with
    rules := [.body (.speedAbove 100000) (.translate ⟨1, 0, 0⟩)] }).isSome

/-! ## Protected mode -/

/-- Whether protected mode accepted, repaired or rejected the event. -/
def decisionKind (w : World) (e : EnvironmentEvent) : String :=
  match decideEvent w e with
  | .accepted _ => "accepted"
  | .repaired _ _ => "repaired"
  | .rejected _ => "rejected"

#guard decisionKind oneBody (.changeMaxSpeed (-1)) == "rejected"
#guard decisionKind oneBody (.changeMaxSpeed 1) == "accepted"
#guard decisionKind oneBody (.changeRestitution 5) == "repaired"
#guard decisionKind oneBody (.addRule (scaleRule 1000)) == "repaired"
#guard decisionKind oneBody (.addRule (.body .all (.scaleMass (-1)))) == "rejected"
#guard decisionKind oneBody (.spawnBody (testBody 0 ⟨0, 0, 0⟩ Vec3.zero)) == "repaired" ||
  decisionKind oneBody (.spawnBody (testBody 0 ⟨0, 0, 0⟩ Vec3.zero)) == "rejected"
-- A body with no mass cannot be repaired.
#guard decisionKind oneBody (.spawnBody (testBody 5 ⟨0, 0, 0⟩ Vec3.zero 0)) == "rejected"
-- Any force law at all is permitted.
#guard decisionKind oneBody (.setPairForce strangeLaw) == "accepted"
-- Unprotected mode lets the same event through and the guarantee really breaks.
#guard !decide (BoundedVelocity (step oneBody (.changeMaxSpeed (-1))))

/-- A universe that would reach a population of 3 with one more spawn. -/
def crowded : World :=
  testWorld [testBody 0 ⟨0, 0, 0⟩ Vec3.zero, testBody 1 ⟨5, 0, 0⟩ Vec3.zero]

-- Enforcing a population limit refuses the change that would break it.
#guard (enforcedStep [.population .le 2] crowded (.spawnBody (testBody 2 ⟨1, 0, 0⟩ Vec3.zero))).bodies.length == 2
#guard (enforcedStep [.population .le 3] crowded (.spawnBody (testBody 2 ⟨1, 0, 0⟩ Vec3.zero))).bodies.length == 3

/-! ## Randomness -/

-- The same seed gives the same events; different seeds give different ones.
#guard safeEvents 42 20 == safeEvents 42 20
#guard safeEvents 42 20 != safeEvents 43 20
#guard wildEvents 42 20 == wildEvents 42 20
-- The generated worlds have what they should.
#guard decide (Guaranteed (generateWorld 492018))
#guard (generateWorld 1).bodies.length ≥ 3

/-! ## Conservation audit -/

#guard (auditMass {} (testWorld [testBody 0 ⟨0, 0, 0⟩ Vec3.zero])).status == .proven
#guard (auditMass {} (testWorld [testBody 0 ⟨0, 0, 0⟩ Vec3.zero] { testLaws with massRate := 1 / 2 })).status == .counterexample
#guard (auditEnergy {} (testWorld [testBody 0 ⟨0, 0, 0⟩ ⟨1, 0, 0⟩] { testLaws with gravity := Vec3.zero })).status == .proven
-- Gravity adds energy, and the audit finds the run that shows it.
#guard (auditEnergy {} oneBody).status == .counterexample
#guard (auditInteractionMomentum (strangeWorld 1)).1 == .proven
#guard (auditInteractionMomentum (strangeWorld 0)).1 == .counterexample

end Paradox

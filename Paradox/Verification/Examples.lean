import Paradox.Start

/-!
# Sanity checks on the theorems

These guard against theorems that are true for uninteresting reasons:

* Each main theorem is applied to the real starting universe with every hypothesis proved.
* Each promise is shown to reject a bad universe.
* The `#guard`s pin exact results and check each card flips when the laws say it should.
-/

namespace Paradox

/-! ## The hypotheses can be met -/

theorem startWorld_wellFormed : WellFormed startWorld := by
  refine ⟨?_, ?_⟩
  · norm_num [LawsOk, startWorld, startLaws]
  · simp only [startWorld, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      norm_num [BodyOk, Bounds.Valid, Bounds.inset]

/-- The speed limit theorem applies to the starting universe, with the limiter on. -/
example : WithinSpeedLimit (tick { startWorld with laws.limiter := true }) :=
  speedLimit_holds startWorld_wellFormed.1 (Or.inl rfl)

/-- The inside theorem applies under wild laws: gravity 1000, bounciness 5, multiplier 1000. -/
example : StaysInside (run 50 { startWorld with
    laws := { startLaws with gravity := 1000, restitution := 5, multiplier := 1000 } }) := by
  refine stays_inside_forever_of_tick 49 ?_
  exact ⟨by norm_num [LawsOk, startLaws], startWorld_wellFormed.2⟩

/-- The energy theorem applies with every force off. -/
example : totalEnergy (run 100 { startWorld with
    laws := { startLaws with gravity := 0, restitution := 1 } }).bodies ≤ totalEnergy startWorld.bodies :=
  energy_forever 100 ⟨by norm_num [LawsOk, startLaws], startWorld_wellFormed.2⟩
    (by norm_num [EnergySafe, startLaws])

/-! ## The promises reject bad universes -/

/-- A sphere for tests. -/
def testBody (p v : Vec3) : Body := ⟨0, p, v, 1, 1 / 2⟩

/-- A universe with these objects. -/
def testWorld (bodies : List Body) (l : Laws := startLaws) : World :=
  { startWorld with bodies, laws := l }

example : ¬ StaysInside (testWorld [testBody ⟨10, 0, 0⟩ Vec3.zero]) := by
  norm_num [StaysInside, testWorld, testBody, startWorld, Bounds.Contains, Bounds.inset]

example : ¬ WithinSpeedLimit (testWorld [testBody ⟨0, 0, 0⟩ ⟨31, 0, 0⟩]) := by
  norm_num [WithinSpeedLimit, Vec3.WithinAbs, testWorld, testBody, startLaws]

example : ¬ SpeedSafe { startLaws with multiplier := 100 } := by
  norm_num [SpeedSafe, startLaws]

example : ¬ MomentumSafe { startLaws with pull := 1, thirdLaw := false } := by
  simp [MomentumSafe]

example : ¬ EnergySafe startLaws := by
  norm_num [EnergySafe, startLaws]

/-! ## Exact physics -/

/-- The first body's position and velocity. -/
def first (w : World) : Option (Vec3 × Vec3) :=
  w.bodies.head?.map fun b => (b.position, b.velocity)

/-- Exact laws for tests: no rounding, time step 1/10, bounciness 1/2. -/
def exactLaws : Laws :=
  { startLaws with
    timeStep := 1 / 10
    restitution := 1 / 2
    grid := 0 }

-- Falling under gravity.
#guard first (tick (testWorld [testBody ⟨0, 5, 0⟩ ⟨1, 0, 0⟩] exactLaws)) ==
  some (⟨1 / 10, 49 / 10, 0⟩, ⟨1, -1, 0⟩)
-- A wall stops an object and it bounces at half speed.
#guard first (tick (testWorld [testBody ⟨19 / 2, 0, 0⟩ ⟨10, 0, 0⟩] { exactLaws with gravity := 0 })) ==
  some (⟨19 / 2, 0, 0⟩, ⟨-5, 0, 0⟩)
-- The multiplier acts after the move.
#guard first (tick (testWorld [testBody ⟨0, 0, 0⟩ ⟨1, 0, 0⟩]
    { exactLaws with gravity := 0, multiplier := 100 })) == some (⟨1 / 10, 0, 0⟩, ⟨100, 0, 0⟩)
-- The limiter acts last.
#guard first (tick (testWorld [testBody ⟨0, 0, 0⟩ ⟨1, 0, 0⟩]
    { exactLaws with gravity := 0, multiplier := 100, limiter := true })) ==
  some (⟨1 / 10, 0, 0⟩, ⟨30, 0, 0⟩)
-- Rounding goes toward zero both ways, and 0 means no rounding.
#guard snap 8 (3 / 16) == 1 / 8
#guard snap 8 (-3 / 16) == -1 / 8
#guard snap 0 (3 / 16) == 3 / 16

/-- Two objects at rest, three apart, with this pull and third law. -/
def pair (pull : ℚ) (third : Bool) : World :=
  testWorld [⟨0, ⟨0, 0, 0⟩, Vec3.zero, 2, 1 / 2⟩, ⟨1, ⟨3, 0, 0⟩, Vec3.zero, 3, 1 / 2⟩]
    { exactLaws with gravity := 0, pull, thirdLaw := third }

-- The theorem's prediction shows up in exact arithmetic, and so does its failure.
#guard decide (MomentumKept (pair 5 true))
#guard !decide (MomentumKept (pair 5 false))
#guard decide (MomentumKept (pair 0 false))

/-! ## Cards flip when the laws say so -/

/-- The start universe under different laws. -/
def under (f : Laws → Laws) : World :=
  { startWorld with laws := f startLaws }

/-- The status of a promise under different laws. -/
def statusUnder (p : Promise) (f : Laws → Laws) : Status :=
  (verdict p (under f)).1

-- Objects stay inside under anything.
#guard statusUnder .staysInside id == .proven
#guard statusUnder .staysInside (fun l => { l with gravity := 1000, restitution := 5, multiplier := 1000 }) == .proven
-- The headline: ×100 breaks the speed limit, and ×100 with the limiter is proved safe.
#guard statusUnder .speedLimit id == .proven
#guard statusUnder .speedLimit (fun l => { l with multiplier := 100 }) == .counterexample
#guard statusUnder .speedLimit (fun l => { l with multiplier := 100, limiter := true }) == .proven
-- Bouncy walls break it too. A slow world cannot show this, so the test universe does.
#guard statusUnder .speedLimit (fun l => { l with restitution := 2 }) == .counterexample
-- Neither law is safe here, but together they cancel out, so the answer is honestly Unproven.
#guard statusUnder .speedLimit (fun l => { l with restitution := 2, multiplier := 1 / 10 }) == .unproven
-- Momentum depends on the third law, not on the strength of the pull.
#guard statusUnder .momentum (fun l => { l with pull := 500 }) == .proven
#guard statusUnder .momentum (fun l => { l with pull := 5, thirdLaw := false }) == .counterexample
#guard statusUnder .momentum (fun l => { l with thirdLaw := false }) == .proven
-- Energy cannot be promised alongside gravity.
#guard statusUnder .energy id == .counterexample
#guard statusUnder .energy (fun l => { l with gravity := 0 }) == .proven
#guard statusUnder .energy (fun l => { l with gravity := 0, pull := 1 }) == .counterexample
#guard statusUnder .energy (fun l => { l with gravity := 0, multiplier := 3 }) == .counterexample

/-! ## Counterexamples are checked -/

/-- The counterexample for the ×100 rule. -/
def times100 : Option Trace :=
  (verdict .speedLimit (under fun l => { l with multiplier := 100 })).2

#guard times100.isSome
#guard times100.any (checkTrace .speedLimit)
-- A tampered trace fails: the states are not what the model produces.
#guard times100.any fun t =>
  !checkTrace .speedLimit { t with states := t.states.map fun s => { s with tick := s.tick + 1 } }
-- A real trace does not count against a promise it does not break.
#guard times100.any fun t => !checkTrace .staysInside t
-- A broken start does not count as a fair run.
#guard !checkTrace .speedLimit ⟨testWorld [testBody ⟨0, 0, 0⟩ ⟨99, 0, 0⟩], []⟩

/-! ## The lock -/

#guard decideLaws { startLaws with gravity := 50 } == .accepted { startLaws with gravity := 50 }
#guard decideLaws { startLaws with multiplier := 100 } ==
  .repaired { startLaws with multiplier := 100, limiter := true }
#guard decideLaws { startLaws with restitution := 2 } ==
  .repaired { startLaws with restitution := 2, limiter := true }
#guard decideLaws { startLaws with maxSpeed := -1 } == .refused
#guard decideLaws { startLaws with restitution := -1 } == .refused

end Paradox

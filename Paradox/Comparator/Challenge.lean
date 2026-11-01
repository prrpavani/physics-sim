import Paradox.Verdict

/-!
# The statements PARADOX stands behind

This file is for reading. It lists the main results, with no proofs. `Solution.lean` proves these exact
statements, and `lake comparator` checks that independently of the rest of the project.

Do not import this file: every `sorry` here is deliberate and is replaced in `Solution.lean`.
-/

namespace Paradox.Comparator

open Paradox

/-- Objects stay inside the world, whatever the laws are. -/
theorem stays_inside {w : World} (h : WellFormed w) : StaysInside (tick w) :=
  sorry

/-- Objects stay inside at every step. -/
theorem stays_inside_forever (n : Nat) {w : World} (h : WellFormed w) (hs : StaysInside w) :
    StaysInside (run n w) :=
  sorry

/-- The speed limit holds after every step, if the laws are speed safe. -/
theorem speedLimit_holds {w : World} (hok : LawsOk w.laws) (hs : SpeedSafe w.laws) :
    WithinSpeedLimit (tick w) :=
  sorry

/-- The speed limit holds at every step. -/
theorem speedLimit_forever (n : Nat) {w : World} (h : WellFormed w) (hs : SpeedSafe w.laws)
    (hv : WithinSpeedLimit w) : WithinSpeedLimit (run n w) :=
  sorry

/-- With Newton's third law on, the pull keeps total momentum along any direction. -/
theorem momentum_holds (l : Laws) (hl : MomentumSafe l) (c : Vec3) (bs : List Body)
    (hm : ∀ b ∈ bs, 0 < b.mass) : totalMomentum c (pullStage l bs) = totalMomentum c bs :=
  sorry

/-- Momentum between objects is kept at every step. -/
theorem momentum_forever (n : Nat) {w : World} (h : WellFormed w) (hs : MomentumSafe w.laws) :
    MomentumKept (run n w) :=
  sorry

/-- With nothing pushing and nothing adding speed, energy can never rise. -/
theorem energy_never_rises {w : World} (hw : WellFormed w) (hs : EnergySafe w.laws) :
    totalEnergy (tick w).bodies ≤ totalEnergy w.bodies :=
  sorry

/-- Energy never rises, over any number of steps. -/
theorem energy_forever (n : Nat) {w : World} (h : WellFormed w) (hs : EnergySafe w.laws) :
    totalEnergy (run n w).bodies ≤ totalEnergy w.bodies :=
  sorry

/-- Between the walls, a move is exactly position plus time times velocity. -/
theorem free_motion {e dt lo hi p v : ℚ} (h1 : lo ≤ p + dt * v) (h2 : p + dt * v ≤ hi) :
    moveAxis e dt lo hi p v = (p + dt * v, v) :=
  sorry

/-- At a wall, an object stops there and its velocity becomes -e · v. -/
theorem wall_bounce {e dt lo hi p v : ℚ} (h1 : lo ≤ p + dt * v) (h2 : hi < p + dt * v) :
    moveAxis e dt lo hi p v = (hi, -(e * v)) :=
  sorry

/-- A checked counterexample is real. -/
theorem checkTrace_sound {p : Promise} {t : Trace} (h : checkTrace p t = true) :
    FairStart t.start ∧ ¬ p.Holds t.start (run t.states.length t.start) :=
  sorry

/-- A Proven card is correct. -/
theorem verdict_proven_sound {p : Promise} {w : World} (h : (verdict p w).1 = .proven) (n : Nat) :
    p.Holds w (run (n + 1) w) :=
  sorry

/-- A counterexample on a card has passed the checker. -/
theorem verdict_counterexample_sound {p : Promise} {w : World} {t : Trace}
    (h : (verdict p w).2 = some t) : checkTrace p t = true :=
  sorry

/-- With the lock on, nothing anyone does can break the speed limit. -/
theorem locked_run_safe (w : World) (changes : List (Option Laws)) (hw : WellFormed w)
    (hs : SpeedSafe w.laws) (hv : WithinSpeedLimit w) : WithinSpeedLimit (lockedRun w changes) :=
  sorry

end Paradox.Comparator

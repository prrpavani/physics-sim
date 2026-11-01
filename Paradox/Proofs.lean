import Paradox.Verification.Facts

/-!
# The proofs

The app shows these theorems exactly as written here. The server reads this file, so what you see on
screen is what Lean compiled. Each block is separated by a blank line.
-/

namespace Paradox

/-- **Objects stay inside the world, whatever the laws are.** -/
theorem stays_inside {w : World} (h : WellFormed w) : StaysInside (tick w) := by
  intro b' hb'
  obtain ⟨b, hb, rfl⟩ := mem_tick hb'
  have hfit := forcesStage_forall (Q := BodyOk w.bounds) (fun _ _ hx => hx) _ _ h.2 b hb
  exact Bounds.contains_clampPoint hfit.2 _

/-- **The speed limit holds after every step, if the laws are speed safe.** Either the limiter acts
last, or neither walls nor the multiplier can add speed. -/
theorem speedLimit_holds {w : World} (hok : LawsOk w.laws) (hs : SpeedSafe w.laws) :
    WithinSpeedLimit (tick w) := by
  have hm := hok.1.le
  intro b' hb'
  obtain ⟨b, -, rfl⟩ := mem_tick hb'
  unfold finishBody
  dsimp only
  split
  · exact Vec3.withinAbs_clampAbs _ hm
  · rename_i hl
    obtain hs | ⟨he, hk⟩ := hs
    · exact absurd hs hl
    · exact scale_withinAbs hk (moved_withinAbs b hm hok.2.2 he)

/-- **With Newton's third law on, the pull between objects keeps total momentum along any direction,
for any pull strength and any masses.** -/
theorem momentum_holds (l : Laws) (hl : MomentumSafe l) (c : Vec3) (bs : List Body)
    (hm : ∀ b ∈ bs, 0 < b.mass) : totalMomentum c (pullStage l bs) = totalMomentum c bs :=
  pairAll_total (Q := fun b => b.mass * b.velocity.dot c) (G := fun b => 0 < b.mass)
    (fun a b ha hb => pullPair_positive l a b ha hb)
    (fun a b ha hb => pullPair_momentum l hl c a b ha hb) bs hm

/-- **With nothing pushing and nothing adding speed, energy can never rise**, however objects hit the
walls. -/
theorem energy_never_rises {w : World} (hw : WellFormed w) (hs : EnergySafe w.laws) :
    totalEnergy (tick w).bodies ≤ totalEnergy w.bodies := by
  have hforces := forcesStage_of_energySafe hs w.bodies
  show total energyOf (((forcesStage w.laws w.bodies).map (limitSpeed w.laws) |>.map
    (moveBody w)).map (finishBody w.laws)) ≤ total energyOf w.bodies
  rw [hforces, List.map_map, List.map_map]
  exact total_map_le w.bodies (fun b => 0 < b.mass) (fun b hb => (hw.2 b hb).1)
    (fun _ hb => step_energy_le hw.1 hs hb)

/-- **A wall never speeds an object up**, if bounciness is from 0 to 1. -/
theorem wall_never_speeds_up {e : ℚ} (dt lo hi p v : ℚ) (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    |(moveAxis e dt lo hi p v).2| ≤ |v| :=
  abs_moveAxis_snd_le dt lo hi p v h0 h1

/-- **Between the walls, a move is exactly position plus time times velocity.** The limits only act
when they must. -/
theorem free_motion {e dt lo hi p v : ℚ} (h1 : lo ≤ p + dt * v) (h2 : p + dt * v ≤ hi) :
    moveAxis e dt lo hi p v = (p + dt * v, v) := by
  simp [moveAxis, not_lt.mpr h1, not_lt.mpr h2]

/-- **At a wall, an object stops there and its velocity becomes `-e · v`.** -/
theorem wall_bounce {e dt lo hi p v : ℚ} (h1 : lo ≤ p + dt * v) (h2 : hi < p + dt * v) :
    moveAxis e dt lo hi p v = (hi, -(e * v)) := by
  simp [moveAxis, not_lt.mpr h1, h2]

/-! ## Over any number of steps -/

/-- **Objects stay inside at every step.** -/
theorem stays_inside_forever (n : Nat) {w : World} (h : WellFormed w) (hs : StaysInside w) :
    StaysInside (run n w) := by
  induction n generalizing w with
  | zero => exact hs
  | succ k ih => exact ih (tick_wellFormed h) (stays_inside h)

/-- **Objects are inside after the next step and every step after, from any valid universe.** -/
theorem stays_inside_forever_of_tick (n : Nat) {w : World} (h : WellFormed w) :
    StaysInside (run (n + 1) w) :=
  stays_inside_forever n (tick_wellFormed h) (stays_inside h)

/-- **The speed limit holds at every step.** -/
theorem speedLimit_forever (n : Nat) {w : World} (h : WellFormed w) (hs : SpeedSafe w.laws)
    (hv : WithinSpeedLimit w) : WithinSpeedLimit (run n w) := by
  induction n generalizing w with
  | zero => exact hv
  | succ k ih => exact ih (tick_wellFormed h) hs (speedLimit_holds h.1 hs)

/-- **Momentum between objects is kept at every step.** -/
theorem momentum_forever (n : Nat) {w : World} (h : WellFormed w) (hs : MomentumSafe w.laws) :
    MomentumKept (run n w) := by
  intro c _
  have hw := run_wellFormed n h
  have hl : MomentumSafe (run n w).laws := by rw [run_laws]; exact hs
  exact momentum_holds _ hl c _ fun b hb => (hw.2 b hb).1

/-- **Energy never rises, over any number of steps.** -/
theorem energy_forever (n : Nat) {w : World} (h : WellFormed w) (hs : EnergySafe w.laws) :
    totalEnergy (run n w).bodies ≤ totalEnergy w.bodies := by
  induction n generalizing w with
  | zero => exact le_rfl
  | succ k ih => exact (ih (tick_wellFormed h) hs).trans (energy_never_rises h hs)

end Paradox

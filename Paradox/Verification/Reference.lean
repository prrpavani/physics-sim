import Paradox.Verification.Facts

/-!
# The limits only act when they must

The bounds in `tick` come from limiting values, so someone could ask whether `tick` does anything
else. These theorems compare it to plain textbook motion: when nothing hits a limit, it is exactly
free motion. When a body hits a wall, it is exactly a bounce.
-/

namespace Paradox

/-- Limiting a value already in range changes nothing. -/
theorem clamp_of_mem {x lo hi : ℚ} (h1 : lo ≤ x) (h2 : x ≤ hi) : clamp x lo hi = x := by
  unfold clamp
  rw [min_eq_left h2, max_eq_right h1]

/-- With no grid, rounding changes nothing. -/
theorem snap_zero (x : ℚ) : snap 0 x = x := by
  simp [snap]

/-- Between the walls, a body moves `dt * v` and keeps its velocity. -/
theorem moveAxis_free {e dt lo hi p v : ℚ} (h1 : lo ≤ p + dt * v) (h2 : p + dt * v ≤ hi) :
    moveAxis .box e dt lo hi p v = (p + dt * v, v) := by
  simp [moveAxis, not_lt.mpr h1, not_lt.mpr h2]

/-- Past the low wall, a body stops at the wall and bounces. -/
theorem moveAxis_bounce_low {e dt lo hi p v : ℚ} (h : p + dt * v < lo) :
    moveAxis .box e dt lo hi p v = (lo, -(e * v)) := by
  simp [moveAxis, h]

/-- Past the high wall, a body stops at the wall and bounces. -/
theorem moveAxis_bounce_high {e dt lo hi p v : ℚ} (h1 : lo ≤ p + dt * v) (h2 : hi < p + dt * v) :
    moveAxis .box e dt lo hi p v = (hi, -(e * v)) := by
  simp [moveAxis, not_lt.mpr h1, h2]

/-- In a torus, a body keeps its velocity at the boundary. -/
theorem moveAxis_torus_velocity (e dt lo hi p v : ℚ) :
    (moveAxis .torus e dt lo hi p v).2 = v := by
  simp only [moveAxis]
  split <;> rfl

/-- Wrapping lands exactly in the interval, so nothing else has to catch it. -/
theorem wrap_mem {lo hi : ℚ} (h : lo < hi) (x : ℚ) :
    lo ≤ wrap lo hi x ∧ wrap lo hi x ≤ hi := by
  have hw : 0 < hi - lo := by linarith
  unfold wrap
  simp only [h, if_true]
  have h1 := Int.floor_le ((x - lo) / (hi - lo))
  have h2 := Int.lt_floor_add_one ((x - lo) / (hi - lo))
  have h3 : ((⌊(x - lo) / (hi - lo)⌋ : ℤ) : ℚ) * (hi - lo) ≤ x - lo := by
    rwa [le_div_iff₀ hw] at h1
  have h4 : x - lo < (((⌊(x - lo) / (hi - lo)⌋ : ℤ) : ℚ) + 1) * (hi - lo) := by
    rwa [div_lt_iff₀ hw] at h2
  constructor <;> nlinarith

/-- **Free motion.** With no grid, no portals, and a target inside the room, one move is exactly
position plus time times velocity, at the same velocity, on every axis. -/
theorem moveBody_free {w : World} {b : Body}
    (hgrid : w.laws.grid = 0) (hportals : w.portals = []) (hbox : w.laws.topology = .box)
    (hregions : w.regions = []) (hrate : w.laws.massRate = 1)
    (hx : (w.bounds.inset b.extent).minX ≤ b.position.x + w.laws.timeStep * b.velocity.x ∧
      b.position.x + w.laws.timeStep * b.velocity.x ≤ (w.bounds.inset b.extent).maxX)
    (hy : (w.bounds.inset b.extent).minY ≤ b.position.y + w.laws.timeStep * b.velocity.y ∧
      b.position.y + w.laws.timeStep * b.velocity.y ≤ (w.bounds.inset b.extent).maxY)
    (hz : (w.bounds.inset b.extent).minZ ≤ b.position.z + w.laws.timeStep * b.velocity.z ∧
      b.position.z + w.laws.timeStep * b.velocity.z ≤ (w.bounds.inset b.extent).maxZ) :
    moveBody w b = { b with position := b.position.add (b.velocity.scale w.laws.timeStep) } := by
  have hdt : w.laws.timeStep * timeScaleAt w.regions b.position = w.laws.timeStep := by
    simp [timeScaleAt, hregions]
  unfold moveBody
  simp only [hdt, hbox, hgrid, hportals, hrate, one_mul, moveAxis_free hx.1 hx.2,
    moveAxis_free hy.1 hy.2, moveAxis_free hz.1 hz.2]
  have hportal : ∀ p v : Vec3, throughPortals [] p v = (p, v) := fun _ _ => rfl
  simp only [hportal, Vec3.snap, snap_zero, Bounds.clampPoint, Vec3.add, Vec3.scale,
    clamp_of_mem hx.1 hx.2, clamp_of_mem hy.1 hy.2, clamp_of_mem hz.1 hz.2]

/-- A velocity already within the limit is not changed by the speed limit. -/
theorem limitSpeed_of_withinAbs {laws : PhysicsLaws} {b : Body}
    (h : b.velocity.WithinAbs laws.maxSpeed) : limitSpeed laws b = b := by
  have key : ∀ x : ℚ, |x| ≤ laws.maxSpeed → clampAbs x laws.maxSpeed = x := fun x hx =>
    clamp_of_mem (abs_le.mp hx).1 (abs_le.mp hx).2
  simp [limitSpeed, Vec3.clampAbs, key _ h.1, key _ h.2.1, key _ h.2.2]

end Paradox

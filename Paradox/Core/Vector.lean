import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Floor

/-!
# Exact-rational vectors and clamping

All formal quantities are exact rationals (`ℚ`). Floating point never appears in the model.
-/

namespace Paradox

/-- Restrict `x` to the interval `[lo, hi]`. Only meaningful when `lo ≤ hi`. -/
def clamp (x lo hi : ℚ) : ℚ :=
  max lo (min x hi)

theorem le_clamp (x lo hi : ℚ) : lo ≤ clamp x lo hi :=
  le_max_left _ _

theorem clamp_le (x : ℚ) {lo hi : ℚ} (h : lo ≤ hi) : clamp x lo hi ≤ hi :=
  max_le h (min_le_right _ _)

/-- Restrict `x` to `[-m, m]`. -/
def clampAbs (x m : ℚ) : ℚ :=
  clamp x (-m) m

theorem abs_clampAbs_le (x : ℚ) {m : ℚ} (hm : 0 ≤ m) : |clampAbs x m| ≤ m :=
  abs_le.mpr ⟨le_clamp _ _ _, clamp_le _ (by linarith)⟩

/-- Round `x` toward zero to a multiple of `1 / n`. Used after a bounce, so that repeated bounces
do not make the exact fractions grow without limit. -/
def roundTowardZero (n : ℕ) (x : ℚ) : ℚ :=
  if 0 ≤ x then (⌊x * n⌋ : ℚ) / n else -((⌊-x * n⌋ : ℚ) / n)

/-- Rounding toward zero never makes a number larger in size. -/
theorem abs_roundTowardZero_le (n : ℕ) (x : ℚ) : |roundTowardZero n x| ≤ |x| := by
  unfold roundTowardZero
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  split_ifs with hx
  · have h0 : (0 : ℚ) ≤ ⌊x * n⌋ := by exact_mod_cast Int.floor_nonneg.mpr (by positivity)
    rw [abs_of_nonneg (div_nonneg h0 hn'.le), abs_of_nonneg hx, div_le_iff₀ hn']
    exact Int.floor_le _
  · push Not at hx
    have h0 : (0 : ℚ) ≤ ⌊-x * n⌋ := by
      exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg (by linarith) hn'.le)
    rw [abs_neg, abs_of_nonneg (div_nonneg h0 hn'.le), abs_of_neg hx, div_le_iff₀ hn']
    exact Int.floor_le _

/-- A point, velocity or acceleration in 3D space. -/
structure Vec3 where
  x : ℚ
  y : ℚ
  z : ℚ
  deriving DecidableEq, Repr

namespace Vec3

/-- The vector with every component equal to zero. -/
def zero : Vec3 := ⟨0, 0, 0⟩

/-- Add two vectors, one component at a time. -/
def add (a b : Vec3) : Vec3 :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

/-- Multiply every component by `k`. -/
def scale (k : ℚ) (a : Vec3) : Vec3 :=
  ⟨k * a.x, k * a.y, k * a.z⟩

/-- The vector pointing the opposite way. -/
def neg (a : Vec3) : Vec3 :=
  ⟨-a.x, -a.y, -a.z⟩

/-- Component-wise `clampAbs`. -/
def clampAbs (a : Vec3) (m : ℚ) : Vec3 :=
  ⟨Paradox.clampAbs a.x m, Paradox.clampAbs a.y m, Paradox.clampAbs a.z m⟩

/-- Every component of `a` has absolute value at most `m`. -/
def WithinAbs (a : Vec3) (m : ℚ) : Prop :=
  |a.x| ≤ m ∧ |a.y| ≤ m ∧ |a.z| ≤ m

theorem withinAbs_clampAbs (a : Vec3) {m : ℚ} (hm : 0 ≤ m) : (a.clampAbs m).WithinAbs m :=
  ⟨abs_clampAbs_le _ hm, abs_clampAbs_le _ hm, abs_clampAbs_le _ hm⟩

/-- A vector can only be within a limit if that limit is non-negative. -/
theorem WithinAbs.limit_nonneg {a : Vec3} {m : ℚ} (h : a.WithinAbs m) : 0 ≤ m :=
  (abs_nonneg _).trans h.1

end Vec3

end Paradox

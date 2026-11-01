import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith

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

/-- Subtract `b` from `a`, one component at a time. -/
def sub (a b : Vec3) : Vec3 :=
  ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

/-- The dot product of two vectors. -/
def dot (a b : Vec3) : ℚ :=
  a.x * b.x + a.y * b.y + a.z * b.z

/-- The cross product of two vectors. -/
def cross (a b : Vec3) : Vec3 :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

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

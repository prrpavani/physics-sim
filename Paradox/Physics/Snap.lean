import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Positivity
import Paradox.Core.Vector

/-!
# The precision grid

Exact rationals can grow without limit as a simulation runs, because bounces and collisions divide.
Rounding to a grid keeps them small. Rounding is toward zero, so it never makes a value larger in
size. That is why speed and energy limits survive it.
-/

namespace Paradox

/-- Round `x` toward zero to a multiple of `1 / n`. If `n` is 0, leave `x` as it is. -/
def snap (n : Nat) (x : ℚ) : ℚ :=
  if n = 0 then x
  else if 0 ≤ x then (⌊x * n⌋ : ℚ) / n
  else -((⌊(-x) * n⌋ : ℚ) / n)

/-- Rounding a non-negative value down gives a value from 0 up to the original. -/
private theorem snap_nonneg_bounds {n : Nat} (hn : n ≠ 0) {y : ℚ} (hy : 0 ≤ y) :
    0 ≤ (⌊y * n⌋ : ℚ) / n ∧ (⌊y * n⌋ : ℚ) / n ≤ y := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  constructor
  · have : (0 : ℤ) ≤ ⌊y * n⌋ := Int.floor_nonneg.mpr (mul_nonneg hy hn'.le)
    have : (0 : ℚ) ≤ (⌊y * n⌋ : ℚ) := by exact_mod_cast this
    positivity
  · rw [div_le_iff₀ hn']
    exact Int.floor_le _

/-- Rounding never makes a value larger in size. -/
theorem abs_snap_le (n : Nat) (x : ℚ) : |snap n x| ≤ |x| := by
  unfold snap
  split_ifs with h0 hx
  · exact le_rfl
  · obtain ⟨h1, h2⟩ := snap_nonneg_bounds h0 hx
    rw [abs_of_nonneg h1, abs_of_nonneg hx]
    exact h2
  · have hx' : 0 ≤ -x := by linarith
    obtain ⟨h1, h2⟩ := snap_nonneg_bounds h0 hx'
    rw [abs_neg, abs_of_nonneg h1, abs_of_neg (by linarith)]
    exact h2

/-- Round every component of a vector. -/
def Vec3.snap (n : Nat) (a : Vec3) : Vec3 :=
  ⟨Paradox.snap n a.x, Paradox.snap n a.y, Paradox.snap n a.z⟩

end Paradox

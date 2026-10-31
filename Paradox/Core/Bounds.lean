import Paradox.Core.Vector

namespace Paradox

/-- An axis-aligned box. -/
structure Bounds where
  minX : ℚ
  maxX : ℚ
  minY : ℚ
  maxY : ℚ
  minZ : ℚ
  maxZ : ℚ
  deriving DecidableEq, Repr

namespace Bounds

/-- The box is non-empty on every axis. -/
def Valid (b : Bounds) : Prop :=
  b.minX ≤ b.maxX ∧ b.minY ≤ b.maxY ∧ b.minZ ≤ b.maxZ

/-- The point `p` lies inside the box. Boundary points count as inside. -/
def Contains (b : Bounds) (p : Vec3) : Prop :=
  (b.minX ≤ p.x ∧ p.x ≤ b.maxX) ∧
  (b.minY ≤ p.y ∧ p.y ≤ b.maxY) ∧
  (b.minZ ≤ p.z ∧ p.z ≤ b.maxZ)

/-- Move `p` to the nearest point of the box, one axis at a time. -/
def clampPoint (b : Bounds) (p : Vec3) : Vec3 :=
  ⟨clamp p.x b.minX b.maxX, clamp p.y b.minY b.maxY, clamp p.z b.minZ b.maxZ⟩

theorem contains_clampPoint {b : Bounds} (h : b.Valid) (p : Vec3) :
    b.Contains (b.clampPoint p) :=
  ⟨⟨le_clamp _ _ _, clamp_le _ h.1⟩,
   ⟨le_clamp _ _ _, clamp_le _ h.2.1⟩,
   ⟨le_clamp _ _ _, clamp_le _ h.2.2⟩⟩

/-- A box containing any point at all is valid. -/
theorem Contains.valid {b : Bounds} {p : Vec3} (h : b.Contains p) : b.Valid :=
  ⟨h.1.1.trans h.1.2, h.2.1.1.trans h.2.1.2, h.2.2.1.trans h.2.2.2⟩

end Bounds

end Paradox

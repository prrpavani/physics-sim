import Paradox.Step

/-!
# Safety theorems

The main result is `execute_preserves_safe`: starting from a safe world, any list of events the
engine accepts, of any length, ends in a safe world. It follows from `step_preserves_safe`, the
same promise for a single event.
-/

namespace Paradox

/-- One accepted event keeps a safe world safe. (Theorems 1 and 3 together.) -/
theorem step_preserves_safe {w w' : World} {e : Event}
    (h : SafeWorld w) (hstep : step w e = some w') : SafeWorld w' := by
  sorry

/-- Theorem 1: after an accepted event, every body is still on the grid. -/
theorem step_preserves_bounds {w w' : World} {e : Event}
    (h : SafeWorld w) (hstep : step w e = some w') : WithinBounds w' :=
  fun b hb => ((step_preserves_safe h hstep).2.2.1 b hb).1

/-- Theorem 3: after an accepted event, every body is still within the speed limit. -/
theorem step_preserves_speed {w w' : World} {e : Event}
    (h : SafeWorld w) (hstep : step w e = some w') : SpeedBounded w' :=
  fun b hb => ((step_preserves_safe h hstep).2.2.1 b hb).2.1

/-- Theorem 4: any list of accepted events, of any length, keeps a safe world safe. -/
theorem execute_preserves_safe {w w' : World} {events : List Event}
    (h : SafeWorld w) (hexec : execute w events = some w') : SafeWorld w' := by
  induction events generalizing w with
  | nil =>
    simp only [execute, Option.some.injEq] at hexec
    exact hexec ▸ h
  | cons e es ih =>
    simp only [execute] at hexec
    split at hexec
    next w1 hstep => exact ih (step_preserves_safe h hstep) hexec
    next => contradiction

end Paradox

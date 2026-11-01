import Paradox.Engine.System

/-!
# A second domain: an ecosystem

This file shares nothing with the physics code except the generic engine. A meadow has rabbits and
grass. It shows that the engine's results apply to any universe, not only to physics.
-/

namespace Paradox.Domains

open Engine

/-- The state of a meadow. -/
structure Meadow where
  rabbits : Nat
  grass : Nat
  deriving DecidableEq, Repr

/-- The limit on rabbits. -/
def rabbitLimit : Nat := 100

/-- The meadow's constraint: at most `rabbitLimit` rabbits. -/
def Valid (m : Meadow) : Prop :=
  m.rabbits ≤ rabbitLimit

instance : DecidablePred Valid := fun m => by unfold Valid; infer_instance

/-- Things that can happen in a meadow. -/
inductive MeadowEvent where
  /-- Grass grows by this much. -/
  | rain (amount : Nat)
  /-- Rabbits breed, using one unit of grass per new rabbit. -/
  | breed
  /-- Some rabbits leave. -/
  | migrate (count : Nat)
  /-- Rabbits arrive from outside. -/
  | arrive (count : Nat)
  deriving DecidableEq, Repr

/-- What each event does. -/
def meadowStep (m : Meadow) : MeadowEvent → Meadow
  | .rain a => { m with grass := m.grass + a }
  | .breed =>
    let born := min m.grass (min m.rabbits (rabbitLimit - m.rabbits))
    { rabbits := m.rabbits + born, grass := m.grass - born }
  | .migrate c => { m with rabbits := m.rabbits - c }
  | .arrive c => { m with rabbits := m.rabbits + c }

/-- Arrivals must fit within the limit. -/
def meadowAllowed (m : Meadow) : MeadowEvent → Prop
  | .arrive c => m.rabbits + c ≤ rabbitLimit
  | _ => True

/-- Each permitted event keeps the rabbit limit. -/
theorem meadow_preservesAll : PreservesAll Valid meadowStep meadowAllowed := by
  intro m e hm ha
  cases e with
  | rain a => exact hm
  | breed =>
    show m.rabbits + min m.grass (min m.rabbits (rabbitLimit - m.rabbits)) ≤ rabbitLimit
    have h1 : min m.grass (min m.rabbits (rabbitLimit - m.rabbits)) ≤ rabbitLimit - m.rabbits :=
      Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
    have h2 : m.rabbits ≤ rabbitLimit := hm
    omega
  | migrate c =>
    show m.rabbits - c ≤ rabbitLimit
    have h : m.rabbits ≤ rabbitLimit := hm
    omega
  | arrive c => exact ha

/-- **The generic engine gives the ecosystem its multi-step result**, with no new induction. -/
theorem meadow_run (m : Meadow) (events : List MeadowEvent) (hm : Valid m)
    (ht : AllowedTrace meadowStep meadowAllowed m events) :
    Valid (runEvents meadowStep m events) :=
  run_preserves meadow_preservesAll m events hm ht

/-- The rejected case is real: an arrival over the limit breaks the constraint. -/
example : ¬ Valid (meadowStep ⟨100, 0⟩ (.arrive 1)) := by decide

/-- The hypotheses can be met. -/
example : Valid (runEvents meadowStep ⟨2, 5⟩ [.rain 3, .breed, .migrate 1]) :=
  meadow_run _ _ (by decide) ⟨trivial, trivial, trivial, trivial⟩

end Paradox.Domains

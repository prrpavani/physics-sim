import Paradox.Verification.Examples

open Paradox

/-- Runs the formal transition function as compiled code and prints exact rational states. -/
def main : IO Unit := do
  let events : List EnvironmentEvent :=
    [.idle, .reverseGravity, .changeMaxSpeed (1 / 2), .disableGravity]
  let mut w := demoWorld
  for e in events do
    w := step w e
    IO.println s!"{repr e}"
    for b in w.bodies do
      IO.println s!"  position {repr b.position}"
      IO.println s!"  velocity {repr b.velocity}"

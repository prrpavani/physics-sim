import Paradox

open Paradox

/-- For now: print a generated world, then run it for a few ticks. The web server comes later. -/
def main (args : List String) : IO Unit := do
  let seed := (args.head? >>= String.toNat?).getD 492018
  let mut w := generateWorld seed
  IO.println s!"Universe #{seed}: {w.width} × {w.height}, {w.bodies.length} bodies, \
    {w.portals.length} portals, gravity ({w.gravity.x}, {w.gravity.y})"
  for _ in [0:5] do
    match step w .move with
    | some w' =>
      w := w'
      let spots := w.bodies.map fun b => s!"({b.pos.x},{b.pos.y})"
      IO.println s!"tick {w.tick}: {String.intercalate " " spots}"
    | none => IO.println "rejected"

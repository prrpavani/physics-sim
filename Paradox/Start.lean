import Paradox.Verdict

namespace Paradox

/-- The laws of the universe people start in. -/
def startLaws : Laws where
  gravity := -10
  pull := 0
  thirdLaw := true
  restitution := 9 / 10
  multiplier := 1
  limiter := false
  maxSpeed := 30
  timeStep := 1 / 50
  grid := 4096

/-- The universe people start in: six spheres in a 20 × 20 × 20 box. -/
def startWorld : World where
  bodies :=
    [ ⟨0, ⟨-5, 6, 2⟩, ⟨4, 0, 1⟩, 1, 1 / 2⟩,
      ⟨1, ⟨3, 3, -4⟩, ⟨-3, 2, 2⟩, 2, 3 / 5⟩,
      ⟨2, ⟨0, -2, 5⟩, ⟨2, 5, -3⟩, 1, 1 / 2⟩,
      ⟨3, ⟨6, 7, 6⟩, ⟨-5, -1, -2⟩, 4, 4 / 5⟩,
      ⟨4, ⟨-6, -4, -6⟩, ⟨1, 3, 4⟩, 1, 1 / 2⟩,
      ⟨5, ⟨2, 8, -1⟩, ⟨0, -2, 6⟩, 8, 1⟩ ]
  bounds := ⟨-10, 10, -10, 10, -10, 10⟩
  laws := startLaws
  tick := 0

end Paradox

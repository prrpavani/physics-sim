import Paradox.Core.World
import Paradox.Physics.Pairwise

namespace Paradox

/-- Add one step of gravity to a body's velocity. -/
def applyGravity (l : Laws) (b : Body) : Body :=
  { b with velocity := b.velocity.add ⟨0, l.timeStep * l.gravity, 0⟩ }

/-- The pull between two objects for one step: `dt · G · m₁ · m₂ / (1 + r²)`. It acts along the line
between them. -/
def pullAmount (l : Laws) (a b : Body) : ℚ :=
  let n := b.position.sub a.position
  l.timeStep * l.pull * (a.mass * b.mass) / (1 + n.dot n)

/-- Apply the pull to two objects. `a` feels it. `b` feels the opposite pull only if Newton's third
law is on. -/
def pullPair (l : Laws) (a b : Body) : Body × Body :=
  let n := b.position.sub a.position
  let f := pullAmount l a b
  ({ a with velocity := a.velocity.add (n.scale (f / a.mass)) },
   if l.thirdLaw then { b with velocity := b.velocity.sub (n.scale (f / b.mass)) } else b)

/-- Apply the pull between every pair of objects. -/
def pullStage (l : Laws) (bs : List Body) : List Body :=
  pairAll (pullPair l) bs

end Paradox

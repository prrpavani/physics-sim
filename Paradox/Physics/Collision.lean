import Paradox.Core.World
import Paradox.Physics.Pairwise

/-!
# Collisions between bodies

Two bodies touch when their centres are closer than the sum of their sizes. No square root is
needed, so every calculation stays exact. `CollisionMode` chooses what touching does.
-/

namespace Paradox

/-- The two bodies are touching. Bodies at exactly the same point count as touching. -/
def Touching (a b : Body) : Prop :=
  let n := b.position.sub a.position
  n.dot n ≤ (a.extent + b.extent) * (a.extent + b.extent)

instance (a b : Body) : Decidable (Touching a b) := by unfold Touching; infer_instance

/-- Bounce two touching bodies off each other with restitution `e`. Bodies that are moving apart,
or at exactly the same point, do not change. Only velocities change. -/
def bouncePair (e : ℚ) (a b : Body) : Body × Body :=
  let n := b.position.sub a.position
  let nn := n.dot n
  let approach := (a.velocity.sub b.velocity).dot n
  if Touching a b ∧ 0 < nn ∧ 0 < approach then
    let k := (1 + e) * (approach / nn) / (a.mass + b.mass)
    ({ a with velocity := a.velocity.sub (n.scale (k * b.mass)) },
     { b with velocity := b.velocity.add (n.scale (k * a.mass)) })
  else
    (a, b)

/-- Touching bodies swap velocities. -/
def exchangeVelocityPair (a b : Body) : Body × Body :=
  if Touching a b then ({ a with velocity := b.velocity }, { b with velocity := a.velocity })
  else (a, b)

/-- Touching bodies swap masses. -/
def exchangeMassPair (a b : Body) : Body × Body :=
  if Touching a b then ({ a with mass := b.mass }, { b with mass := a.mass })
  else (a, b)

/-- One body made from `a` and `b`. It keeps `a`'s id and position and the larger shape. Mass and
charge add. Its velocity is what keeps total momentum the same. -/
def mergeBodies (a b : Body) : Body :=
  let total := a.mass + b.mass
  { a with
    shape := if b.extent ≤ a.extent then a.shape else b.shape
    velocity := ((a.velocity.scale a.mass).add (b.velocity.scale b.mass)).scale (1 / total)
    mass := total
    charge := a.charge + b.charge }

/-- Add `a` to the list, joining it with the first body it touches. -/
def mergeOne (a : Body) : List Body → List Body
  | [] => [a]
  | c :: cs => if Touching a c then mergeBodies a c :: cs else c :: mergeOne a cs

/-- Join touching bodies, working through the list once. -/
def mergeAll (bs : List Body) : List Body :=
  bs.foldr mergeOne []

/-- The new body created when `a` and `b` touch: `a`'s shape, halfway between them, at rest, with
their average mass. -/
def childOf (id : Nat) (a b : Body) : Body :=
  { a with
    id
    position := (a.position.add b.position).scale (1 / 2)
    velocity := Vec3.zero
    mass := (a.mass + b.mass) / 2
    charge := 0 }

/-- The first touching pair in the list, if there is one. -/
def firstTouchingPair : List Body → Option (Body × Body)
  | [] => none
  | b :: bs =>
    match bs.find? (fun c => decide (Touching b c)) with
    | some c => some (b, c)
    | none => firstTouchingPair bs

/-- Create at most one new body, if a pair is touching and the population limit allows it. Returns
the bodies and the next free id. -/
def spawnStage (limit nextId : Nat) (bs : List Body) : List Body × Nat :=
  if bs.length < limit then
    match firstTouchingPair bs with
    | some (a, b) => (bs ++ [childOf nextId a b], nextId + 1)
    | none => (bs, nextId)
  else (bs, nextId)

/-- Apply the world's collision mode. Returns the bodies and the next free id. -/
def collisionStage (laws : PhysicsLaws) (nextId : Nat) (bs : List Body) : List Body × Nat :=
  match laws.collisions with
  | .none => (bs, nextId)
  | .bounce => (pairAll (bouncePair laws.restitution) bs, nextId)
  | .exchangeVelocity => (pairAll exchangeVelocityPair bs, nextId)
  | .exchangeMass => (pairAll exchangeMassPair bs, nextId)
  | .merge => (mergeAll bs, nextId)
  | .spawn => spawnStage laws.populationLimit nextId bs

end Paradox

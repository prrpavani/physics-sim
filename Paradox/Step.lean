import Paradox.Spec

/-!
# The rules of physics

`step` is the only way a world changes. The app runs this function to animate the world, and
the theorems are about this same function.
-/

namespace Paradox

/-- Cap a velocity component to the range `-m .. m`. -/
def capSpeed (m : Nat) (v : Int) : Int := max (-(m : Int)) (min v m)

/-- Cap both components of a velocity. -/
def cap (m : Nat) (v : Vec2) : Vec2 := ⟨capSpeed m v.x, capSpeed m v.y⟩

/-- Move along one axis with cells `0 .. size - 1`, from position `p` with velocity `v`.
Returns the new position and velocity. A body that would leave bounces off the wall: it
lands as far inside as it would have gone outside, and its velocity on this axis flips. -/
def bounce (size : Nat) (p v : Int) : Int × Int :=
  let n := p + v
  if n < 0 then (-n, -v)
  else if n > (size : Int) - 1 then (2 * ((size : Int) - 1) - n, -v)
  else (n, v)

/-- Where a body at `p` ends up: the exit of the first portal whose entrance is `p`, else `p`. -/
def throughPortals (portals : List Portal) (p : Vec2) : Vec2 :=
  match portals.find? (fun portal => portal.entrance = p) with
  | some portal => portal.exit
  | none => p

/-- One tick for one body: gravity changes its velocity (capped), it moves and bounces,
then it goes through a portal if it landed on one. -/
def moveBody (w : World) (b : Body) : Body :=
  let v := cap w.maxSpeed (b.vel + w.gravity)
  let bx := bounce w.width b.pos.x v.x
  let by_ := bounce w.height b.pos.y v.y
  { b with pos := throughPortals w.portals ⟨bx.1, by_.1⟩, vel := ⟨bx.2, by_.2⟩ }

/-- The body with this id, if there is one. -/
def findBody (w : World) (id : Nat) : Option Body := w.bodies.find? (fun b => b.id = id)

/-- Two bodies touch when they are on the same or neighbouring cells. -/
def Touching (a b : Body) : Prop :=
  (a.pos.x - b.pos.x).natAbs ≤ 1 ∧ (a.pos.y - b.pos.y).natAbs ≤ 1

instance (a b : Body) : Decidable (Touching a b) := by unfold Touching; infer_instance

/-- Apply one event. `none` means the event breaks a rule and is rejected; the world is
then unchanged. Each rejection reason is a rule that keeps the world safe. -/
def step (w : World) : Event → Option World
  | .move => some { w with bodies := w.bodies.map (moveBody w), tick := w.tick + 1 }
  | .changeGravity g => some { w with gravity := g }
  | .spawnBody b =>
    -- A new body must be valid and must not reuse an id.
    if ValidBody w b ∧ b.id ∉ w.bodies.map Body.id then
      some { w with bodies := w.bodies ++ [b] }
    else none
  | .removeBody id =>
    if id ∈ w.bodies.map Body.id then
      some { w with bodies := w.bodies.filter (fun b => b.id ≠ id) }
    else none
  | .applyImpulse id dv =>
    if id ∈ w.bodies.map Body.id then
      some { w with bodies := w.bodies.map fun b =>
        if b.id = id then { b with vel := cap w.maxSpeed (b.vel + dv) } else b }
    else none
  | .addPortal p =>
    -- A portal may not lead off the grid.
    if InBounds w p.entrance ∧ InBounds w p.exit then
      some { w with portals := w.portals ++ [p] }
    else none
  | .collide a b =>
    match findBody w a, findBody w b with
    | some ba, some bb =>
      if a ≠ b ∧ ba.mass = bb.mass ∧ Touching ba bb then
        some { w with bodies := w.bodies.map fun x =>
          if x.id = a then { x with vel := bb.vel }
          else if x.id = b then { x with vel := ba.vel }
          else x }
      else none
    | _, _ => none

/-- Apply events in order. If any event is rejected, the whole run is rejected. -/
def execute (w : World) : List Event → Option World
  | [] => some w
  | e :: es =>
    match step w e with
    | some w' => execute w' es
    | none => none

end Paradox

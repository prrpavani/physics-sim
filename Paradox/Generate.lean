import Paradox.Step

/-!
# Random worlds from a seed

The same seed always gives the same world. The safety theorem for this generator covers every
seed, so no seed needs testing.
-/

namespace Paradox

/-- The next number in a simple pseudo-random sequence (a linear congruential generator). -/
def nextSeed (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

def genWidth : Nat := 48
def genHeight : Nat := 32
def genMaxSpeed : Nat := 3

/-- A random number in `-m .. m`. -/
def randRange (m s : Nat) : Int := (s % (2 * m + 1) : Nat) - (m : Int)

/-- Body number `i`, built from seed `s`. -/
def genBody (i s : Nat) : Body :=
  let s1 := nextSeed s
  let s2 := nextSeed s1
  let s3 := nextSeed s2
  let s4 := nextSeed s3
  let s5 := nextSeed s4
  { id := i
    pos := ⟨(s1 % genWidth : Nat), (s2 % genHeight : Nat)⟩
    vel := ⟨randRange genMaxSpeed s3, randRange genMaxSpeed s4⟩
    mass := 1 + s5 % 4 }

/-- A random point on the grid, from seed `s`. -/
def genPoint (s : Nat) : Vec2 :=
  ⟨(nextSeed s % genWidth : Nat), (nextSeed (nextSeed s) % genHeight : Nat)⟩

/-- The world for a seed: 3 to 10 bodies, up to 2 portals, and a random gravity. -/
def generateWorld (seed : Nat) : World :=
  let s := nextSeed seed
  let count := 3 + s % 8
  let portalCount := nextSeed s % 3
  { width := genWidth
    height := genHeight
    maxSpeed := genMaxSpeed
    gravity := ⟨randRange 1 (nextSeed (s + 1)), randRange 1 (nextSeed (s + 2))⟩
    bodies := (List.range count).map fun i => genBody i (s + 7919 * (i + 1))
    portals := (List.range portalCount).map fun j =>
      ⟨genPoint (s + 104729 * (j + 1)), genPoint (s + 104729 * (j + 1) + 1)⟩
    tick := 0 }

end Paradox

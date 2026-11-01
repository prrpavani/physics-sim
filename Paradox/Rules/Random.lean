import Paradox.Verification.Protected

/-!
# Reproducible randomness

Random experiments are pure functions of a seed. The same seed always gives the same events. The
safe generator only makes permitted events, for every seed, so the main theorems cover every random
experiment without any testing.
-/

namespace Paradox

open Engine

/-- The next number in a pseudo-random sequence (a linear congruential generator). -/
def nextSeed (s : Nat) : Nat :=
  (s * 1103515245 + 12345) % 2147483648

/-- A random number `lo`, `lo + step`, `lo + 2 * step`, ... from seed `s`, with `count` choices. -/
def scaled (s count : Nat) (lo stepSize : ℚ) : ℚ :=
  lo + ((s % count : Nat) : ℚ) * stepSize

theorem scaled_bounds (s : Nat) {count : Nat} (hc : 0 < count) {lo stepSize : ℚ}
    (hstep : 0 ≤ stepSize) :
    lo ≤ scaled s count lo stepSize ∧
      scaled s count lo stepSize ≤ lo + ((count - 1 : Nat) : ℚ) * stepSize := by
  have hlt : s % count ≤ count - 1 := Nat.le_sub_one_of_lt (Nat.mod_lt _ hc)
  have hcast : ((s % count : Nat) : ℚ) ≤ ((count - 1 : Nat) : ℚ) := by exact_mod_cast hlt
  have h0 : (0 : ℚ) ≤ ((s % count : Nat) : ℚ) := by positivity
  unfold scaled
  constructor
  · nlinarith
  · nlinarith

/-- A random vector with each component from -`m` to `m`, in steps of 1/8. -/
def randomVector (s : Nat) (m : Nat) : Vec3 :=
  let a := nextSeed s
  let b := nextSeed a
  let c := nextSeed b
  let count := 16 * m + 1
  ⟨scaled a count (-(m : ℚ)) (1 / 8), scaled b count (-(m : ℚ)) (1 / 8),
   scaled c count (-(m : ℚ)) (1 / 8)⟩

/-- The force laws the generator can pick from. -/
def randomForceLaws : List LawExpr :=
  [ .const 0,
    .mul (.const (1 / 2)) (.div (.mul .massA .massB) (.add (.const 1) .distSquared)),
    .neg (.div (.mul .chargeA .chargeB) (.add (.const 1) .distSquared)),
    .mul (.const (1 / 10)) .dist ]

/-- One permitted random event from seed `s`. -/
def safeEventOf (s : Nat) : EnvironmentEvent :=
  let t := nextSeed s
  match s % 12 with
  | 0 => .idle
  | 1 => .changeGravity (randomVector t 20)
  | 2 => .reverseGravity
  | 3 => .disableGravity
  | 4 => .changeMaxSpeed (scaled t 80 (1 / 2) (1 / 2))
  | 5 => .changeMaxAcceleration (scaled t 80 0 (1 / 2))
  | 6 => .changeRestitution (scaled t 11 0 (1 / 10))
  | 7 => .setPairForce (randomForceLaws.getD (t % 4) (.const 0))
  | 8 => .setReaction (scaled t 5 (-1) (1 / 2))
  | 9 => .setTopology (if t % 2 = 0 then .box else .torus)
  | 10 => .setMagnetic (randomVector t 2)
  | _ => .reverseTime

/-- Every generated event is permitted, for every seed and in every world. -/
theorem safeEventOf_allowed (s : Nat) (w : World) : Allowed w (safeEventOf s) := by
  unfold safeEventOf
  dsimp only
  split
  case h_5 =>
    show (0 : ℚ) < _
    have := (scaled_bounds (nextSeed s) (count := 80) (lo := 1 / 2) (stepSize := 1 / 2)
      (by norm_num) (by norm_num)).1
    linarith
  case h_6 =>
    exact (scaled_bounds (nextSeed s) (count := 80) (lo := 0) (stepSize := 1 / 2)
      (by norm_num) (by norm_num)).1
  case h_7 =>
    have h := scaled_bounds (nextSeed s) (count := 11) (lo := 0) (stepSize := 1 / 10)
      (by norm_num) (by norm_num)
    refine ⟨h.1, h.2.trans ?_⟩
    norm_num
  all_goals exact trivial

/-- A reproducible list of `n` permitted events. -/
def safeEvents (seed : Nat) : Nat → List EnvironmentEvent
  | 0 => []
  | n + 1 => safeEventOf seed :: safeEvents (nextSeed seed) n

/-- **Every random experiment is permitted**, for every seed, length and starting world. -/
theorem safeEvents_allowed (seed n : Nat) (w : World) :
    AllowedTrace step Allowed w (safeEvents seed n) := by
  induction n generalizing seed w with
  | zero => exact trivial
  | succ n ih => exact ⟨safeEventOf_allowed seed w, ih _ _⟩

/-- **Random chaos keeps every guarantee**, for every seed. -/
theorem random_chaos_safe (seed n : Nat) (w : World) (h : Guaranteed w) :
    Guaranteed (run w (safeEvents seed n)) :=
  guaranteed_run w _ h (safeEvents_allowed seed n w)

/-- One random event that may break the rules, for unprotected experiments. -/
def wildEventOf (s : Nat) : EnvironmentEvent :=
  let t := nextSeed s
  match s % 8 with
  | 0 => .changeMaxSpeed (scaled t 21 (-5) (1 / 2))
  | 1 => .changeRestitution (scaled t 41 0 (1 / 4))
  | 2 => .setMassRate (scaled t 9 (-1) (1 / 2))
  | 3 => .addRule (.body .all (.scaleVelocity (scaled t 8 2 1)))
  | _ => safeEventOf t

/-- A reproducible list of `n` events that may break the rules. -/
def wildEvents (seed : Nat) : Nat → List EnvironmentEvent
  | 0 => []
  | n + 1 => wildEventOf seed :: wildEvents (nextSeed seed) n

/-! ## Random worlds -/

/-- The laws of a generated universe. -/
def defaultLaws : PhysicsLaws where
  gravity := ⟨0, -10, 0⟩
  fields := []
  maxSpeed := 30
  maxAcceleration := 100
  timeStep := 1 / 50
  restitution := 4 / 5
  pairForce := .const 0
  reaction := 1
  drag := .const 0
  central := .const 0
  magnetic := Vec3.zero
  massRate := 1
  topology := .box
  metric := .euclidean
  collisions := .bounce
  populationLimit := 64
  grid := 4096

/-- The box of a generated universe. -/
def defaultBounds : Bounds :=
  ⟨-10, 10, -10, 10, -10, 10⟩

/-- Body number `i` of a generated universe, from seed `s`. -/
def randomBody (i s : Nat) : Body :=
  let a := nextSeed s
  let b := nextSeed a
  let c := nextSeed b
  let d := nextSeed c
  let e := nextSeed d
  let f := nextSeed e
  let g := nextSeed f
  { id := i
    shape := if g % 2 = 0 then .sphere (1 / 2) else .cube (1 / 2)
    position := ⟨scaled a 153 (-(19 / 2)) (1 / 8), scaled b 153 (-(19 / 2)) (1 / 8),
                 scaled c 153 (-(19 / 2)) (1 / 8)⟩
    velocity := ⟨scaled d 81 (-5) (1 / 8), scaled e 81 (-5) (1 / 8), scaled f 81 (-5) (1 / 8)⟩
    mass := scaled g 8 1 (1 / 2)
    charge := scaled (nextSeed g) 5 (-1) (1 / 2) }

/-- How many bodies the universe for a seed has: 3 to 10. -/
def worldCount (seed : Nat) : Nat :=
  3 + nextSeed seed % 8

/-- The seed for body number `i` of the universe for a seed. -/
def bodySeed (seed i : Nat) : Nat :=
  nextSeed seed + 7919 * (i + 1)

/-- The bodies of the universe for a seed. -/
def worldBodies (seed : Nat) : List Body :=
  (List.range (worldCount seed)).map fun i => randomBody i (bodySeed seed i)

/-- The universe for a seed, in a 20 × 20 × 20 box. -/
def generateWorld (seed : Nat) : World :=
  { bodies := worldBodies seed
    bounds := defaultBounds
    laws := defaultLaws
    regions := []
    portals := []
    rules := []
    tick := 0
    nextId := worldCount seed }

@[simp] theorem generateWorld_bodies (seed : Nat) :
    (generateWorld seed).bodies = worldBodies seed := by
  simp only [generateWorld]

@[simp] theorem generateWorld_nextId (seed : Nat) :
    (generateWorld seed).nextId = worldCount seed := by
  simp only [generateWorld]

theorem worldBodies_mem {seed : Nat} {b : Body} (h : b ∈ worldBodies seed) :
    ∃ i, i < worldCount seed ∧ b = randomBody i (bodySeed seed i) := by
  unfold worldBodies at h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
  exact ⟨i, List.mem_range.mp hi, rfl⟩

theorem worldBodies_ids (seed : Nat) :
    (worldBodies seed).map Body.id = List.range (worldCount seed) := by
  unfold worldBodies
  rw [List.map_map]
  exact List.map_id _

theorem randomBody_extent (i s : Nat) : (randomBody i s).extent = 1 / 2 := by
  simp only [randomBody, Body.extent]
  split <;> rfl

/-- **Every generated universe is safe**, for every seed. -/
theorem generateWorld_guaranteed (seed : Nat) : Guaranteed (generateWorld seed) := by
  have hmem : ∀ b ∈ (generateWorld seed).bodies, ∃ i s, b = randomBody i s := by
    intro b hb
    rw [generateWorld_bodies] at hb
    obtain ⟨i, -, hi⟩ := worldBodies_mem hb
    exact ⟨i, _, hi⟩
  have hsafe : SafeEnvironment (generateWorld seed) := by
    refine ⟨by norm_num [generateWorld, defaultBounds, Bounds.Valid], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · norm_num [generateWorld, defaultLaws]
    · norm_num [generateWorld, defaultLaws]
    · norm_num [generateWorld, defaultLaws]
    · norm_num [generateWorld, defaultLaws]
    · norm_num [generateWorld, defaultLaws]
    · simp [generateWorld]
    · simp [generateWorld]
    · intro b hb
      obtain ⟨i, s, rfl⟩ := hmem b hb
      unfold FitsIn
      rw [randomBody_extent]
      norm_num [generateWorld, defaultBounds, Bounds.Valid, Bounds.inset]
  intro p
  refine ⟨hsafe, ?_, by simp [generateWorld]⟩
  cases p with
  | positiveMass =>
    intro b hb
    obtain ⟨i, s, rfl⟩ := hmem b hb
    have h := (scaled_bounds (nextSeed (nextSeed (nextSeed (nextSeed (nextSeed (nextSeed (nextSeed
      s))))))) (count := 8) (lo := 1) (stepSize := 1 / 2) (by norm_num) (by norm_num)).1
    show 0 < scaled _ 8 1 (1 / 2)
    linarith
  | boundedPosition =>
    intro b hb
    obtain ⟨i, s, rfl⟩ := hmem b hb
    rw [randomBody_extent]
    have key : ∀ r : Nat, -(19 / 2 : ℚ) ≤ scaled r 153 (-(19 / 2)) (1 / 8) ∧
        scaled r 153 (-(19 / 2)) (1 / 8) ≤ 19 / 2 := by
      intro r
      have h := scaled_bounds r (count := 153) (lo := -(19 / 2)) (stepSize := 1 / 8)
        (by norm_num) (by norm_num)
      refine ⟨h.1, h.2.trans ?_⟩
      norm_num
    have room : ∀ r : Nat, (-10 + 1 / 2 : ℚ) ≤ scaled r 153 (-(19 / 2)) (1 / 8) ∧
        scaled r 153 (-(19 / 2)) (1 / 8) ≤ 10 - 1 / 2 := by
      intro r
      have := key r
      constructor <;> linarith [this.1, this.2]
    exact ⟨room _, room _, room _⟩
  | boundedVelocity =>
    intro b hb
    obtain ⟨i, s, rfl⟩ := hmem b hb
    have key : ∀ r : Nat, |scaled r 81 (-5) (1 / 8)| ≤ 30 := by
      intro r
      have h := scaled_bounds r (count := 81) (lo := -5) (stepSize := 1 / 8)
        (by norm_num) (by norm_num)
      refine abs_le.mpr ⟨by linarith [h.1], h.2.trans ?_⟩
      norm_num
    exact ⟨key _, key _, key _⟩
  | safeEnvironment => exact hsafe
  | uniqueIds =>
    constructor
    · simp only [Property.holds, UniqueIds, generateWorld_bodies]
      rw [worldBodies_ids]
      exact List.nodup_range
    · intro b hb
      rw [generateWorld_bodies] at hb
      obtain ⟨i, hi, rfl⟩ := worldBodies_mem hb
      rw [generateWorld_nextId]
      exact hi

end Paradox

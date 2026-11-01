import Paradox.Verification.Preservation

/-!
# Layer A: rule consistency

Can the user's constraints all be true at once, in at least one universe with at least one object?

An empty universe trivially meets every "every object must..." constraint, so `Valid` asks for an
object. The check gives one of three answers:

* A concrete universe that meets all constraints. Lean checks it directly.
* Two constraints that cannot both hold, with a proof that no valid universe exists.
* Unknown: the check found neither. This says nothing about whether the constraints can be met.
-/

namespace Paradox

/-- A comparison. -/
inductive Cmp where
  | lt | le | eq | ge | gt
  deriving DecidableEq, Repr

/-- What the comparison says about `x` and `v`. -/
def Cmp.holds : Cmp → ℚ → ℚ → Prop
  | .lt, x, v => x < v
  | .le, x, v => x ≤ v
  | .eq, x, v => x = v
  | .ge, x, v => v ≤ x
  | .gt, x, v => v < x

instance (c : Cmp) (x v : ℚ) : Decidable (c.holds x v) := by
  cases c <;> unfold Cmp.holds <;> infer_instance

/-- A number measured on every object. -/
inductive BodyQuantity where
  | mass | charge | extent
  | positionX | positionY | positionZ
  | velocityX | velocityY | velocityZ
  /-- The square of the object's speed. Stationary means this is 0. -/
  | speedSquared
  deriving DecidableEq, Repr

/-- The value of the quantity on a body. -/
def BodyQuantity.value : BodyQuantity → Body → ℚ
  | .mass, b => b.mass
  | .charge, b => b.charge
  | .extent, b => b.extent
  | .positionX, b => b.position.x
  | .positionY, b => b.position.y
  | .positionZ, b => b.position.z
  | .velocityX, b => b.velocity.x
  | .velocityY, b => b.velocity.y
  | .velocityZ, b => b.velocity.z
  | .speedSquared, b => b.velocity.dot b.velocity

/-- A number measured on the laws. -/
inductive LawQuantity where
  | gravityX | gravityY | gravityZ
  | maxSpeed | maxAcceleration | restitution | timeStep | massRate | reaction
  deriving DecidableEq, Repr

/-- The value of the quantity in the given laws. -/
def LawQuantity.value : LawQuantity → PhysicsLaws → ℚ
  | .gravityX, l => l.gravity.x
  | .gravityY, l => l.gravity.y
  | .gravityZ, l => l.gravity.z
  | .maxSpeed, l => l.maxSpeed
  | .maxAcceleration, l => l.maxAcceleration
  | .restitution, l => l.restitution
  | .timeStep, l => l.timeStep
  | .massRate, l => l.massRate
  | .reaction, l => l.reaction

/-- A constraint a user can require of their universe. -/
inductive Constraint where
  /-- Every object meets this. -/
  | body (q : BodyQuantity) (c : Cmp) (v : ℚ)
  /-- The number of objects meets this. -/
  | population (c : Cmp) (v : ℚ)
  /-- The laws meet this. -/
  | law (q : LawQuantity) (c : Cmp) (v : ℚ)
  deriving DecidableEq, Repr

/-- What a constraint says about a world. -/
def Constraint.holds : Constraint → World → Prop
  | .body q c v, w => ∀ b ∈ w.bodies, c.holds (q.value b) v
  | .population c v, w => c.holds (w.bodies.length : ℚ) v
  | .law q c v, w => c.holds (q.value w.laws) v

instance (c : Constraint) (w : World) : Decidable (c.holds w) := by
  cases c <;> unfold Constraint.holds <;> infer_instance

/-- Every built-in guarantee holds. -/
def WellFormed (w : World) : Prop :=
  ∀ p ∈ Property.all, p.holds w

instance (w : World) : Decidable (WellFormed w) := by unfold WellFormed; infer_instance

/-- `w` is a valid universe for constraints `cs`: it has the box and speed limit of `base`, at least
one object, every built-in guarantee, and every constraint. -/
def Valid (base : World) (cs : List Constraint) (w : World) : Prop :=
  w.bounds = base.bounds ∧ w.laws.maxSpeed = base.laws.maxSpeed ∧
  w.bodies ≠ [] ∧ WellFormed w ∧ ∀ c ∈ cs, c.holds w

instance (base : World) (cs : List Constraint) (w : World) : Decidable (Valid base cs w) := by
  unfold Valid; infer_instance

/-- Constraints every valid universe meets automatically. -/
def implicitConstraints (base : World) : List Constraint :=
  let b := base.bounds
  let m := base.laws.maxSpeed
  [ .body .mass .gt 0, .body .extent .ge 0, .body .speedSquared .ge 0,
    .body .positionX .ge b.minX, .body .positionX .le b.maxX,
    .body .positionY .ge b.minY, .body .positionY .le b.maxY,
    .body .positionZ .ge b.minZ, .body .positionZ .le b.maxZ,
    .body .velocityX .ge (-m), .body .velocityX .le m,
    .body .velocityY .ge (-m), .body .velocityY .le m,
    .body .velocityZ .ge (-m), .body .velocityZ .le m,
    .population .ge 1, .law .maxSpeed .eq m ]

theorem valid_parts {base : World} {cs : List Constraint} {w : World} (h : Valid base cs w) :
    SafeEnvironment w ∧ PositiveMass w ∧ BoundedPosition w ∧ BoundedVelocity w := by
  have hw := h.2.2.2.1
  exact ⟨hw .safeEnvironment (Property.mem_all _), hw .positiveMass (Property.mem_all _),
    hw .boundedPosition (Property.mem_all _), hw .boundedVelocity (Property.mem_all _)⟩

/-- Every valid universe meets the implicit constraints. -/
theorem implicit_hold {base : World} {cs : List Constraint} {w : World} (h : Valid base cs w) :
    ∀ c ∈ implicitConstraints base, c.holds w := by
  obtain ⟨he, hm, hp, hv⟩ := valid_parts h
  have hbounds := h.1
  have hspeed := h.2.1
  have hne := h.2.2.1
  have hfit : ∀ b ∈ w.bodies, 0 ≤ b.extent := fun b hb => (he.2.2.2.2.2.2.2.2 b hb).1
  have hin : ∀ b ∈ w.bodies, base.bounds.minX ≤ b.position.x ∧ b.position.x ≤ base.bounds.maxX ∧
      base.bounds.minY ≤ b.position.y ∧ b.position.y ≤ base.bounds.maxY ∧
      base.bounds.minZ ≤ b.position.z ∧ b.position.z ≤ base.bounds.maxZ := by
    intro b hb
    have hc := hp b hb
    have he0 := hfit b hb
    rw [hbounds] at hc
    simp only [Bounds.Contains, Bounds.inset] at hc
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩, ⟨a5, a6⟩⟩ := hc
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have hvel : ∀ b ∈ w.bodies, -base.laws.maxSpeed ≤ b.velocity.x ∧
      b.velocity.x ≤ base.laws.maxSpeed ∧ -base.laws.maxSpeed ≤ b.velocity.y ∧
      b.velocity.y ≤ base.laws.maxSpeed ∧ -base.laws.maxSpeed ≤ b.velocity.z ∧
      b.velocity.z ≤ base.laws.maxSpeed := by
    intro b hb
    obtain ⟨v1, v2, v3⟩ := hv b hb
    rw [hspeed] at v1 v2 v3
    have a1 := abs_le.mp v1
    have a2 := abs_le.mp v2
    have a3 := abs_le.mp v3
    exact ⟨a1.1, a1.2, a2.1, a2.2, a3.1, a3.2⟩
  intro c hc
  simp only [implicitConstraints, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact fun b hb => hm b hb
  · exact fun b hb => hfit b hb
  · intro b hb
    show (0 : ℚ) ≤ b.velocity.x * b.velocity.x + b.velocity.y * b.velocity.y +
      b.velocity.z * b.velocity.z
    nlinarith [mul_self_nonneg b.velocity.x, mul_self_nonneg b.velocity.y,
      mul_self_nonneg b.velocity.z]
  · exact fun b hb => (hin b hb).1
  · exact fun b hb => (hin b hb).2.1
  · exact fun b hb => (hin b hb).2.2.1
  · exact fun b hb => (hin b hb).2.2.2.1
  · exact fun b hb => (hin b hb).2.2.2.2.1
  · exact fun b hb => (hin b hb).2.2.2.2.2
  · exact fun b hb => (hvel b hb).1
  · exact fun b hb => (hvel b hb).2.1
  · exact fun b hb => (hvel b hb).2.2.1
  · exact fun b hb => (hvel b hb).2.2.2.1
  · exact fun b hb => (hvel b hb).2.2.2.2.1
  · exact fun b hb => (hvel b hb).2.2.2.2.2
  · have : 1 ≤ w.bodies.length := List.length_pos_iff.mpr hne
    show (1 : ℚ) ≤ (w.bodies.length : ℚ)
    exact_mod_cast this
  · exact hspeed

/-! ## Finding contradictions -/

/-- No number can meet both comparisons. -/
def Cmp.conflicts (c1 : Cmp) (v1 : ℚ) (c2 : Cmp) (v2 : ℚ) : Bool :=
  let isUpper : Cmp → Bool := fun c => c == .lt || c == .le || c == .eq
  let isLower : Cmp → Bool := fun c => c == .gt || c == .ge || c == .eq
  let below (cu : Cmp) (vu : ℚ) (cl : Cmp) (vl : ℚ) : Bool :=
    isUpper cu && isLower cl &&
      (decide (vu < vl) || (decide (vu = vl) && (cu == .lt || cl == .gt)))
  below c1 v1 c2 v2 || below c2 v2 c1 v1

theorem Cmp.conflicts_sound {c1 c2 : Cmp} {v1 v2 : ℚ} (h : Cmp.conflicts c1 v1 c2 v2 = true)
    (x : ℚ) (h1 : c1.holds x v1) (h2 : c2.holds x v2) : False := by
  cases c1 <;> cases c2 <;>
    simp [Cmp.conflicts, Cmp.holds] at h h1 h2 <;>
    (try rcases h with h | h) <;>
    (try rcases h with h | h) <;>
    first | linarith | exact h (h1.symm.trans h2)

/-- The two constraints cannot both hold in a universe with at least one object. -/
def Constraint.conflicts : Constraint → Constraint → Bool
  | .body q1 c1 v1, .body q2 c2 v2 => q1 == q2 && Cmp.conflicts c1 v1 c2 v2
  | .population c1 v1, .population c2 v2 => Cmp.conflicts c1 v1 c2 v2
  | .law q1 c1 v1, .law q2 c2 v2 => q1 == q2 && Cmp.conflicts c1 v1 c2 v2
  | _, _ => false

theorem Constraint.conflicts_sound {a b : Constraint} (h : a.conflicts b = true) {w : World}
    (hne : w.bodies ≠ []) (ha : a.holds w) (hb : b.holds w) : False := by
  cases a <;> cases b <;> simp only [Constraint.conflicts] at h <;> try contradiction
  case body.body q1 c1 v1 q2 c2 v2 =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hc⟩ := h
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
    exact Cmp.conflicts_sound hc _ (ha x hx) (hb x hx)
  case population.population c1 v1 c2 v2 => exact Cmp.conflicts_sound h _ ha hb
  case law.law q1 c1 v1 q2 c2 v2 =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hc⟩ := h
    exact Cmp.conflicts_sound hc _ ha hb

/-- Any two conflicting constraints, stated or implicit, rule out every valid universe. -/
theorem no_valid_of_conflict {base : World} {cs : List Constraint} {a b : Constraint}
    (ha : a ∈ cs ++ implicitConstraints base) (hb : b ∈ cs ++ implicitConstraints base)
    (h : a.conflicts b = true) : ¬ ∃ w, Valid base cs w := by
  rintro ⟨w, hw⟩
  have hold : ∀ c ∈ cs ++ implicitConstraints base, c.holds w := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hw.2.2.2.2 c hc
    · exact implicit_hold hw c hc
  exact Constraint.conflicts_sound h hw.2.2.1 (hold a ha) (hold b hb)

/-- The first conflicting pair among the constraints, if there is one. -/
def findConflict (l : List Constraint) : Option (Constraint × Constraint) :=
  (l.flatMap fun a => l.map fun b => (a, b)).find? fun p => p.1.conflicts p.2

theorem findConflict_spec {l : List Constraint} {a b : Constraint}
    (h : findConflict l = some (a, b)) : a ∈ l ∧ b ∈ l ∧ a.conflicts b = true := by
  have hf := List.find?_some h
  have hm := List.mem_of_find?_eq_some h
  obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp hm
  obtain ⟨y, hy', he⟩ := List.mem_map.mp hy
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨hx, hy', hf⟩

/-! ## Building a witness -/

/-- A value meeting all the comparisons, if one is easy to find. Starts from `fallback`. -/
def pickValue (cmps : List (Cmp × ℚ)) (fallback : ℚ) : ℚ :=
  let good (x : ℚ) : Bool := cmps.all fun p => decide (p.1.holds x p.2)
  let lows := cmps.filterMap fun p => if p.1 == .gt || p.1 == .ge then some p.2 else none
  let highs := cmps.filterMap fun p => if p.1 == .lt || p.1 == .le then some p.2 else none
  let equal := cmps.findSome? fun p => if p.1 == .eq then some p.2 else none
  let lo := lows.foldl max (lows.headD 0)
  let hi := highs.foldl min (highs.headD 0)
  let candidates := equal.toList ++ [fallback, (lo + hi) / 2, lo, hi, lo + 1, hi - 1]
  (candidates.find? good).getD fallback

/-- The comparisons on one body quantity. -/
def bodyCmps (cs : List Constraint) (q : BodyQuantity) : List (Cmp × ℚ) :=
  cs.filterMap fun
    | .body q' c v => if q' == q then some (c, v) else none
    | _ => none

/-- The comparisons on one law quantity. -/
def lawCmps (cs : List Constraint) (q : LawQuantity) : List (Cmp × ℚ) :=
  cs.filterMap fun
    | .law q' c v => if q' == q then some (c, v) else none
    | _ => none

/-- The comparisons on the number of objects. -/
def populationCmps (cs : List Constraint) : List (Cmp × ℚ) :=
  cs.filterMap fun
    | .population c v => some (c, v)
    | _ => none

/-- Candidate velocities along the x axis to try for the speed constraints. -/
def speedCandidates (cs : List Constraint) : List ℚ :=
  (bodyCmps cs .speedSquared).flatMap fun p => [approxSqrt p.2, approxSqrt p.2 + 1 / 1024]

/-- A candidate universe built from the constraints. `candidateX` overrides the x velocity. -/
def buildWitness (base : World) (cs : List Constraint) (candidateX : Option ℚ) : World :=
  let pick := fun q (fallback : ℚ) => pickValue (bodyCmps cs q) fallback
  let lawPick := fun q (fallback : ℚ) => pickValue (lawCmps cs q) fallback
  let b := base.bounds
  let extent := pick .extent (1 / 2)
  let body (id : Nat) : Body :=
    { id
      shape := .sphere extent
      position :=
        ⟨pick .positionX ((b.minX + b.maxX) / 2), pick .positionY ((b.minY + b.maxY) / 2),
         pick .positionZ ((b.minZ + b.maxZ) / 2)⟩
      velocity := ⟨candidateX.getD (pick .velocityX 0), pick .velocityY 0, pick .velocityZ 0⟩
      mass := pick .mass 1
      charge := pick .charge 0 }
  let count := (⌈pickValue ((.ge, 1) :: populationCmps cs) 1⌉).toNat
  let l := base.laws
  { base with
    bodies := (List.range (min count 256)).map body
    rules := []
    nextId := min count 256
    laws := { l with
      gravity := ⟨lawPick .gravityX l.gravity.x, lawPick .gravityY l.gravity.y,
                  lawPick .gravityZ l.gravity.z⟩
      maxAcceleration := lawPick .maxAcceleration l.maxAcceleration
      restitution := lawPick .restitution l.restitution
      timeStep := lawPick .timeStep l.timeStep
      massRate := lawPick .massRate l.massRate
      reaction := lawPick .reaction l.reaction } }

/-- The result of the rule consistency check. -/
inductive RuleCheck where
  /-- This concrete universe meets everything. -/
  | satisfiable (witness : World)
  /-- These two constraints cannot both hold. -/
  | contradiction (a b : Constraint)
  /-- The check found neither a universe nor a contradiction. -/
  | unknown
  deriving Repr

/-- Check that a set of constraints can all be true together. -/
def checkConstraints (base : World) (cs : List Constraint) : RuleCheck :=
  match findConflict (cs ++ implicitConstraints base) with
  | some (a, b) => .contradiction a b
  | none =>
    let candidates := none :: (speedCandidates cs).map some
    match (candidates.map (buildWitness base cs)).find? (fun w => decide (Valid base cs w)) with
    | some w => .satisfiable w
    | none => .unknown

/-- **A witness is real.** If the check returns a universe, that universe is valid. -/
theorem checkConstraints_satisfiable {base : World} {cs : List Constraint} {w : World}
    (h : checkConstraints base cs = .satisfiable w) : Valid base cs w := by
  unfold checkConstraints at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    next x hx =>
      simp only [RuleCheck.satisfiable.injEq] at h
      subst h
      have hp := List.find?_some hx
      simpa using hp
    next => simp at h

/-- **A contradiction is real.** If the check names two constraints, no valid universe exists. -/
theorem checkConstraints_contradiction {base : World} {cs : List Constraint} {a b : Constraint}
    (h : checkConstraints base cs = .contradiction a b) : ¬ ∃ w, Valid base cs w := by
  unfold checkConstraints at h
  split at h
  next x y hx =>
    simp only [RuleCheck.contradiction.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, h2, h3⟩ := findConflict_spec hx
    exact no_valid_of_conflict h1 h2 h3
  next =>
    dsimp only at h
    split at h <;> simp at h

end Paradox

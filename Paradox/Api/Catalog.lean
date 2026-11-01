import Paradox.Api.Json

/-!
# What the proof explorer and preset menu show

Theorem names are written with double backticks, so the build fails if a listed theorem does not
exist. Each entry says in plain language what the theorem establishes, and what it does not.
-/

namespace Paradox.Api

open Lean (Json)

/-- One theorem as shown to users. -/
structure TheoremInfo where
  id : Lean.Name
  layer : String
  statement : String
  assumptions : List String
  doesNotSay : String

/-- The theorems behind PARADOX's answers. -/
def theorems : List TheoremInfo :=
  [ ⟨``run_inv, "evolution",
      "A guarantee that holds at the start still holds after any finite list of permitted events.",
      ["The guarantee holds at the start.", "The environment is safe at the start.",
       "Every rule has passed the rule checker for this guarantee.", "Every event is permitted."],
      "Anything about events that are not permitted."⟩,
    ⟨``protectedRun_safe, "evolution",
      "In protected mode, no list of events can break a guarantee.",
      ["The guarantee holds at the start.", "The environment is safe at the start.",
       "Every rule has passed the rule checker for this guarantee."],
      "That events are carried out as written: unsafe ones are repaired or rejected."⟩,
    ⟨``next_inv, "evolution",
      "A guarantee holds whatever order the rules run in.",
      ["The guarantee holds at the start.", "The environment is safe at the start.",
       "Every rule has passed the rule checker.", "The event is permitted."],
      "That every order gives the same world."⟩,
    ⟨``enforcedRun_holds, "evolution",
      "Any constraint can be enforced: the universe refuses changes that would break it.",
      ["The constraints hold at the start."],
      "That the laws would keep the constraint without enforcement. The universe may freeze."⟩,
    ⟨``random_chaos_safe, "evolution",
      "Every seeded random experiment keeps every guarantee, for every seed.",
      ["All guarantees hold at the start."],
      "Anything about the unsafe generator."⟩,
    ⟨``generateWorld_guaranteed, "evolution",
      "The universe generated from any seed starts with every guarantee true.",
      [], "Anything about worlds edited after generation."⟩,
    ⟨``Rule.keeps_sound, "evolution",
      "If the rule checker clears a rule for a guarantee, the rule keeps that guarantee.",
      ["The environment is safe."],
      "That a rule the checker does not clear is unsafe. It may be safe."⟩,
    ⟨``pairForces_conserve_momentum, "evolution",
      "With Newton's third law on, every invented force law keeps total momentum.",
      ["The reaction factor is 1.", "Every mass is positive."],
      "Anything about walls, gravity or other outside forces, which do change momentum."⟩,
    ⟨``interaction_conserves_momentum, "evolution",
      "Forces between bodies and momentum-keeping collisions never change total momentum.",
      ["The reaction factor is 1.", "Every mass is positive.",
       "Collisions bounce, merge or pass through."],
      "Anything about a full step, where walls and gravity also act."⟩,
    ⟨``bouncePair_energy_elastic, "evolution",
      "A bounce at restitution 1 keeps the energy of two bodies exactly.",
      ["Both masses are positive."], "Anything about energy over a full step."⟩,
    ⟨``idleRun_energy_le, "evolution",
      "With no forces, total kinetic energy can only stay level or fall as time passes.",
      ["No rules, forces or events.", "Bodies bounce or pass through each other.",
       "The environment is safe.", "The mass rate is at most 1."],
      "That energy is conserved exactly. Grid rounding and walls can remove it."⟩,
    ⟨``idleRun_conserves_mass, "evolution",
      "Total mass stays the same as time passes.",
      ["No rules or events.", "The mass rate is 1.", "Collisions do not create bodies.",
       "Every mass is positive."], "Anything about events, which can add or remove bodies."⟩,
    ⟨``moveBody_free, "evolution",
      "When nothing is hit, a move is exactly position plus time times velocity.",
      ["No grid, regions or portals.", "Box topology.", "Mass rate 1.",
       "The target is inside the room."],
      "That the model is realistic physics."⟩,
    ⟨``moveAxis_bounce_high, "evolution",
      "A body that hits a wall stops at the wall and its velocity becomes -e times what it was.",
      ["Box topology."], "Anything about realistic contact."⟩,
    ⟨``checkTrace_sound, "evolution",
      "A trace that passes the checker really happens and really breaks the claim.",
      [], "That a claim with no counterexample found is true."⟩,
    ⟨``proven_excludes_counterexample, "evolution",
      "A proof and a counterexample with permitted events cannot both exist for a guarantee.",
      [], "Anything about counterexamples using events outside the proof's scope."⟩,
    ⟨``checkConstraints_satisfiable, "rule",
      "If a universe is returned, it meets every constraint, has an object and every guarantee.",
      ["The universe has the same box and speed limit as the one checked."],
      "That the universe stays valid over time. That is a separate question."⟩,
    ⟨``checkConstraints_contradiction, "rule",
      "If two constraints are named, no universe with an object can meet them.",
      ["The universe has the same box and speed limit as the one checked."],
      "Anything about an empty universe, which meets every 'every object' constraint."⟩,
    ⟨``LawExpr.divisionsSafe_sound, "transition",
      "A formula that passes the division check has a defined value for every input.",
      ["Mass is positive."], "That a formula failing the check is undefined."⟩,
    ⟨``orderStatus_conflict, "transition",
      "A reported rule conflict is real: the two orders give different results in that world.",
      [], "Anything about other worlds."⟩,
    ⟨``Engine.deterministic_of_function, "transition",
      "A universe that moves by a function always has exactly one next state.",
      [], "That the result is the one the user intended."⟩ ]

/-- A theorem as JSON. -/
def encTheorem (t : TheoremInfo) : Json :=
  Json.mkObj [("id", t.id.toString), ("layer", t.layer), ("statement", t.statement),
    ("assumptions", encList Json.str t.assumptions), ("doesNotSay", t.doesNotSay)]

/-- A ready-made universe. -/
structure Preset where
  name : String
  title : String
  description : String
  change : World → World

/-- A world with changed laws. -/
def lawPreset (f : PhysicsLaws → PhysicsLaws) (w : World) : World :=
  { w with laws := f w.laws }

/-- A box in the middle of the world. -/
def centreBox (size : ℚ) : Bounds :=
  ⟨-size, size, -size, size, -size, size⟩

/-- Force that pulls bodies together as in Newton's gravity: `G m₁ m₂ / r³`, times the line. -/
def newtonForce (g : ℚ) : LawExpr :=
  .div (.mul (.const g) (.mul .massA .massB))
    (.add (.const (1 / 10)) (.mul .distSquared .dist))

/-- Coulomb-style force: like charges push apart. -/
def chargeForce (k : ℚ) : LawExpr :=
  .neg (.div (.mul (.const k) (.mul .chargeA .chargeB))
    (.add (.const (1 / 10)) (.mul .distSquared .dist)))

/-- The ready-made universes. -/
def presets : List Preset :=
  [ ⟨"normal", "Normal Universe", "Gravity pulls down and objects bounce.", id⟩,
    ⟨"lowGravity", "Low Gravity", "Gravity is one tenth as strong.",
      lawPreset fun l => { l with gravity := ⟨0, -1, 0⟩ }⟩,
    ⟨"zeroGravity", "Zero Gravity", "Nothing pulls. Objects drift and bounce.",
      lawPreset fun l => { l with gravity := Vec3.zero }⟩,
    ⟨"strongGravity", "Strong Gravity", "Gravity is five times as strong.",
      lawPreset fun l => { l with gravity := ⟨0, -50, 0⟩ }⟩,
    ⟨"upsideDown", "Upside Down", "Gravity pulls up.",
      lawPreset fun l => { l with gravity := ⟨0, 10, 0⟩ }⟩,
    ⟨"outwardGravity", "Outward Gravity", "Everything is pushed away from the centre of space.",
      lawPreset fun l => { l with gravity := Vec3.zero, central := .const (-(1 / 2)) }⟩,
    ⟨"cosmos", "Cosmos", "Objects attract each other. Space has no favoured direction.",
      lawPreset fun l =>
        { l with gravity := Vec3.zero, pairForce := newtonForce 20, collisions := .merge }⟩,
    ⟨"charged", "Charged Particles", "Like charges repel in a magnetic field.",
      lawPreset fun l =>
        { l with gravity := Vec3.zero, pairForce := chargeForce 20, magnetic := ⟨0, 2, 0⟩ }⟩,
    ⟨"noThirdLaw", "No Third Law", "Objects are pulled, but nothing pulls back. Momentum breaks.",
      lawPreset fun l =>
        { l with gravity := Vec3.zero, pairForce := newtonForce 20, reaction := 0 }⟩,
    ⟨"torus", "Looping Space", "Leave one side and come back on the other.",
      lawPreset fun l => { l with gravity := Vec3.zero, topology := .torus, collisions := .none }⟩,
    ⟨"taxicab", "Taxicab Space", "Force depends on distance measured along the axes.",
      lawPreset fun l =>
        { l with gravity := Vec3.zero, pairForce := newtonForce 20, metric := .manhattan }⟩,
    ⟨"merging", "Sticky Universe", "Objects that touch join into one.",
      lawPreset fun l => { l with collisions := .merge }⟩,
    ⟨"spawning", "Fertile Universe", "Objects that touch create a new object.",
      lawPreset fun l => { l with gravity := Vec3.zero, collisions := .spawn }⟩,
    ⟨"decay", "Decaying Mass", "Every object slowly loses mass.",
      lawPreset fun l => { l with massRate := 999 / 1000 }⟩,
    ⟨"antiFriction", "Anti-Friction", "Moving objects speed up on their own, up to the limit.",
      lawPreset fun l => { l with gravity := Vec3.zero, drag := .const (-(1 / 5)) }⟩,
    ⟨"slowTime", "Slow Time Zone", "Time runs at one fifth speed in the blue centre region.",
      fun w => { w with
        laws := { w.laws with gravity := Vec3.zero }
        regions := [⟨"slow", "blue", centreBox 4, 1 / 5⟩] }⟩,
    ⟨"portals", "Portal Universe", "A portal at the bottom sends objects to the top, turned.",
      fun w => { w with
        portals := [⟨⟨-10, 10, -10, -8, -10, 10⟩, some ⟨0, 8, 0⟩, .rotate⟩] }⟩,
    ⟨"heavyWhenFast", "Heavier When Faster", "An object's mass grows with its speed.",
      fun w => { w with
        laws := { w.laws with gravity := Vec3.zero }
        rules := [.body .all (.setMassFormula (.add (.const 1) (.mul (.const (1 / 100)) .speedSquared)))] }⟩,
    ⟨"chaotic", "Chaotic Universe", "Gravity flips every 50 steps, with negative drag.",
      fun w => { w with
        laws := { w.laws with drag := .const (-(1 / 10)) }
        rules := [.when (.everyTicks 50) (.world .reverseGravity)] }⟩,
    ⟨"protected", "Protected Universe", "A speed limiter runs after every step, on top of normal laws.",
      fun w => { w with rules := [.body .all .clampVelocity] }⟩ ]

/-- A preset as JSON. -/
def encPreset (p : Preset) : Json :=
  Json.mkObj [("name", p.name), ("title", p.title), ("description", p.description)]

/-- The universe from a preset and seed. -/
def presetWorld (p : Preset) (seed : Nat) : World :=
  p.change (generateWorld seed)

end Paradox.Api

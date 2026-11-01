// PARADOX wire contract, version 1.0.0. See docs/API.md.
//
// The backend is the only authority on what happens in a universe. The frontend may interpolate
// between frames for drawing, but it must not compute physics of its own.

/** An exact rational: "49/10", "-3". Requests may also use "0.5" or a JSON number. */
export type Rational = string;
export type RationalInput = string | number;

export interface Vec3 { x: Rational; y: Rational; z: Rational }

export interface Bounds {
  minX: Rational; maxX: Rational;
  minY: Rational; maxY: Rational;
  minZ: Rational; maxZ: Rational;
}

export type Shape =
  | { type: "sphere"; radius: Rational }
  | { type: "cube"; halfWidth: Rational };

export interface Body {
  id: number;
  shape: Shape;
  position: Vec3;
  velocity: Vec3;
  mass: Rational;
  charge: Rational;
  /** For drawing only. Floating-point approximations, never formal values. Ignored on input. */
  renderPosition?: [number, number, number];
  renderVelocity?: [number, number, number];
  renderSize?: number;
}

/** A formula for inventing force laws. "A" is the body acted on and "B" is the other body. */
export type LawExpr =
  | { type: "const"; value: Rational }
  | { type: "massA" | "massB" | "chargeA" | "chargeB" | "distSquared" | "dist" | "speedSquared" }
  | { type: "add" | "sub" | "mul" | "div"; a: LawExpr; b: LawExpr }
  | { type: "neg"; a: LawExpr }
  | { type: "pow"; a: LawExpr; n: number };

export interface Field { region: Bounds; acceleration: Vec3 }
export interface Region { name: string; color: string; box: Bounds; timeScale: Rational }
export type PortalEffect =
  | { type: "none" | "reverse" | "rotate" }
  | { type: "scale"; factor: Rational };
/** `exit: null` is allowed. The consistency check reports it as underspecified. */
export interface Portal { entrance: Bounds; exit: Vec3 | null; effect: PortalEffect }

export type Topology = "box" | "torus";
export type Metric = "euclidean" | "manhattan" | "chebyshev";
export type CollisionMode = "none" | "bounce" | "exchangeVelocity" | "exchangeMass" | "merge" | "spawn";

export interface PhysicsLaws {
  gravity: Vec3;
  fields: Field[];
  maxSpeed: Rational;
  maxAcceleration: Rational;
  timeStep: Rational;
  restitution: Rational;
  pairForce: LawExpr;
  /** 1 is Newton's third law. */
  reaction: Rational;
  drag: LawExpr;
  central: LawExpr;
  magnetic: Vec3;
  massRate: Rational;
  topology: Topology;
  metric: Metric;
  collisions: CollisionMode;
  populationLimit: number;
  /** Positions and velocities are multiples of 1/grid. 0 means exact, which can grow very large. */
  grid: number;
}

export type BodyCond =
  | { type: "all" }
  | { type: "inBox" | "entersBox"; box: Bounds }
  | { type: "inRegion"; name: string }
  | { type: "onColor"; color: string }
  | { type: "speedAbove"; speed: Rational }
  | { type: "not"; condition: BodyCond };

export type BodyAction =
  | { type: "applyForce"; force: Vec3 }
  | { type: "reverseVelocity" | "rotateVelocity" | "clampVelocity" | "clampPosition" }
  | { type: "scaleVelocity" | "scaleMass"; factor: Rational }
  | { type: "translate"; by: Vec3 }
  | { type: "setMassFormula"; formula: LawExpr }
  | { type: "setCharge"; charge: Rational };

export type WorldCond =
  | { type: "always" | "gravityChanged" }
  | { type: "gravityAbove"; value: Rational }
  | { type: "everyTicks"; n: number }
  | { type: "not"; condition: WorldCond };

export type WorldAction =
  | { type: "setGravity"; gravity: Vec3 }
  | { type: "reverseGravity" }
  | { type: "setMaxSpeed" | "setReaction" | "setMassRate"; value: Rational }
  | { type: "setPairForce"; formula: LawExpr };

export type Rule =
  | { type: "skip" }
  | { type: "body"; condition?: BodyCond; action: BodyAction }
  | { type: "world"; action: WorldAction }
  | { type: "destroy"; condition: BodyCond }
  | { type: "create"; template: Body }
  | { type: "seq"; first: Rule; then: Rule }
  | { type: "when"; condition: WorldCond; rule: Rule };

export interface World {
  bodies: Body[];
  bounds: Bounds;
  laws: PhysicsLaws;
  regions: Region[];
  portals: Portal[];
  rules: Rule[];
  tick: number;
  nextId: number;
}

export type EnvironmentEvent =
  | { type: "idle" | "reverseGravity" | "disableGravity" | "clearFields" | "reverseTime"
      | "clearRegions" | "clearPortals" | "clearRules" }
  | { type: "changeGravity"; gravity: Vec3 }
  | { type: "changeMaxSpeed" | "changeMaxAcceleration" | "changeRestitution" | "changeTimeStep"
      | "setReaction" | "setMassRate"; value: Rational }
  | { type: "changeBounds"; bounds: Bounds }
  | { type: "addField"; field: Field }
  | { type: "setPairForce" | "setDrag" | "setCentral"; formula: LawExpr }
  | { type: "setMagnetic"; field: Vec3 }
  | { type: "setTopology"; topology: Topology }
  | { type: "setMetric"; metric: Metric }
  | { type: "setCollisions"; mode: CollisionMode }
  | { type: "setPopulationLimit" | "setGrid"; value: number }
  | { type: "spawnBody"; body: Body }
  | { type: "removeBody"; id: number }
  | { type: "applyImpulse"; id: number; impulse: Vec3 }
  | { type: "setBodyState"; id: number; position: Vec3; velocity: Vec3 }
  | { type: "addRegion"; region: Region }
  | { type: "addPortal"; portal: Portal }
  | { type: "addRule"; rule: Rule };

export type Property =
  | "positiveMass" | "boundedPosition" | "boundedVelocity" | "safeEnvironment" | "uniqueIds";

export type Cmp = "lt" | "le" | "eq" | "ge" | "gt";
export type BodyQuantity = "mass" | "charge" | "extent" | "positionX" | "positionY" | "positionZ"
  | "velocityX" | "velocityY" | "velocityZ" | "speedSquared";
export type LawQuantity = "gravityX" | "gravityY" | "gravityZ" | "maxSpeed" | "maxAcceleration"
  | "restitution" | "timeStep" | "massRate" | "reaction";

export type Constraint =
  | { type: "body"; quantity: BodyQuantity; cmp: Cmp; value: Rational }
  | { type: "population"; cmp: Cmp; value: Rational }
  | { type: "law"; quantity: LawQuantity; cmp: Cmp; value: Rational };

export type Claim =
  | Property
  | { type: "property"; property: Property }
  | { type: "constraint"; constraint: Constraint }
  | { type: "momentumConserved"; direction: Vec3 }
  | { type: "energyNotRising" | "massConserved" | "populationConserved" };

/**
 * proven: Lean checked a theorem establishing this, under the listed assumptions and scope.
 * counterexample: a concrete run, replayed through the formal model, breaks the claim.
 * unknown: neither was established. Never show this as a failure.
 * underspecified: required behaviour is missing, so the simulation is relying on a default.
 * inconsistent: no universe with an object can meet these requirements.
 */
export type Status = "proven" | "counterexample" | "unknown" | "underspecified" | "inconsistent";

/** allowed: only permitted events. any: every event. timeOnly: no events, time passes. */
export type EventScope = "allowed" | "any" | "timeOnly";

export interface Trace {
  initial: World;
  events: EnvironmentEvent[];
  /** The state after each event. Replay these in the viewport. */
  states: World[];
  final: World;
}

export interface Verdict {
  claim: Claim;
  status: Status;
  theoremId: string | null;
  assumptions: string[];
  scope: EventScope | null;
  explanation: string;
  counterexample: Trace | null;
}

export type Decision =
  | { result: "accepted"; event: EnvironmentEvent }
  | { result: "repaired"; original: EnvironmentEvent; event: EnvironmentEvent }
  | { result: "rejected"; event: EnvironmentEvent };

/**
 * What is known about a guarantee in one state.
 * proven: the theorem covers every permitted future from here.
 * unknown: it holds now, but the theorem's conditions do not, so the future is not promised.
 * violated: this state breaks it.
 */
export type GuaranteeStatus = "proven" | "unknown" | "violated";
export type Guarantees = Record<Property, GuaranteeStatus>;

export interface Frame {
  tick: number;
  bodies: Body[];
  /** The event that ran in this step. */
  event: EnvironmentEvent;
  decision: Decision | null;
  guarantees: Guarantees;
}

/** A reproducible chance per step of a random event. rate is out of 1000. */
export interface Chaos { seed: number; rate: number; kind: "safe" | "wild" }

export interface SearchLimits { depth?: number; budget?: number; idleSteps?: number }

export interface StepResponse {
  world: World;
  mode: "protected" | "unprotected";
  decision: Decision | null;
  /** A constraint would have been broken, so the world did not change. */
  frozen: boolean;
  violations: Property[];
  brokenConstraints: Constraint[];
}

export interface RunResponse {
  frames: Frame[];
  world: World;
  guarantees: Guarantees;
  /** Send this as chaos.seed next time, to carry on the same experiment. */
  nextChaosSeed: number | null;
}

export interface FormulaCheck {
  status: Status;
  explanation: string;
  theoremId: string | null;
  /** The force at each distance, for drawing. `force` is null where the formula has no value. */
  samples: { r: number; force: number | null }[];
  momentumConserved: string;
  momentumTheorem: string;
}

export interface RuleLayer {
  status: Status;
  theoremId: string | null;
  checked: string;
  assumptions: string[];
  explanation: string;
  witness?: World;
  conflict?: Constraint[];
}

export interface TransitionLayer {
  status: Status;
  theoremId: string | null;
  checked: string;
  deterministic: boolean;
  deterministicTheorem: string;
  missingRegions: string[];
  portalsWithoutExit: Portal[];
  undefinedFormulas: string[];
  unknownFormulas: string[];
  ruleConflicts: [Rule, Rule][];
  explanation: string;
}

export interface ConsistencyResponse {
  ruleConsistency: RuleLayer;
  transitionConsistency: TransitionLayer;
  evolutionConsistency: { verdicts: Verdict[] };
}

export interface RuleReport {
  rule: Rule;
  status: Status;
  certified: boolean;
  environmentSafe: boolean;
  keeps: { property: Property; cleared: boolean }[];
  missingRegions: string[];
  repair: Rule | null;
  theoremId: string;
  explanation: string;
}

export interface TheoremInfo {
  id: string;
  layer: "rule" | "transition" | "evolution";
  statement: string;
  assumptions: string[];
  /** Show this. It stops the UI implying the theorem applies more widely than it does. */
  doesNotSay: string;
}

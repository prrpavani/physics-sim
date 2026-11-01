// A stand-in for the Lean server, so the front end can be built before the server exists.
// It answers in the format of docs/FRONTEND_CONTRACT.md, but NOTHING it computes is verified:
// it uses floating point, and every guarantee it reports is marked "unproved". The UI shows a
// MOCK badge whenever this file is answering.

import { toNum, toFrac } from "./num.js";

const ABSOLUTE_ZERO = -273;

// ---- Random worlds ----

function rng(seed) {
  let s = seed >>> 0 || 1;
  return () => ((s = (Math.imul(s, 1103515245) + 12345) >>> 0) / 4294967296);
}

export function generateWorld(seed) {
  const r = rng(seed);
  const bodies = [];
  const count = 5 + Math.floor(r() * 6);
  for (let id = 0; id < count; id++) {
    const kind = r();
    const water = kind < 0.8;
    const temperature = water ? [-15, 20, 110][Math.floor(r() * 3)] : 20;
    bodies.push({
      id,
      material: water ? "water" : "rubber",
      phase: water ? phaseOf(temperature, 0, 100) : "solid",
      position: [toFrac(r() * 16 - 8), toFrac(2 + r() * 10), toFrac(r() * 16 - 8)],
      velocity: [toFrac(r() * 6 - 3), toFrac(r() * 4), toFrac(r() * 6 - 3)],
      mass: String(1 + Math.floor(r() * 3)),
      temperature: String(temperature),
    });
  }
  return {
    tick: 0,
    bounds: { min: ["-10", "0", "-10"], max: ["10", "15", "10"] },
    laws: {
      gravity: ["0", "-981/100", "0"],
      maxSpeed: "30",
      maxAcceleration: "40",
      timeStep: "1/60",
      restitution: "7/10",
      drag: "1/200",
      freezingPoint: "0",
      boilingPoint: "100",
      ambientTemperature: "20",
      heatTransfer: "1/100",
    },
    bodies,
  };
}

// ---- Rules ----

function phaseOf(t, freezing, boiling) {
  return t < freezing ? "solid" : t < boiling ? "liquid" : "gas";
}

const clampAbs = (x, m) => Math.max(-m, Math.min(m, x));
const round = x => Math.round(x * 1000) / 1000;

/** Why an event is rejected, or null if it is allowed. */
function rejection(world, e) {
  const L = world.laws;
  if (e.type === "setLaw") {
    const v = toNum(e.value);
    switch (e.law) {
      case "maxSpeed": return v > 0 ? null : ["The speed of light must be above zero.", "speed-limit"];
      case "maxAcceleration": return v >= 0 ? null : ["The force limit can't be negative.", "speed-limit"];
      case "timeStep": return v > 0 ? null : ["Time must move forward.", "in-the-box"];
      case "restitution": return v >= 0 && v <= 1 ? null
        : ["Bounciness must be between 0 and 1, or walls would add energy.", "bounce-no-speedup"];
      case "drag": return v >= 0 && v <= 1 ? null : ["Air friction must be between 0 and 1.", "speed-limit"];
      case "freezingPoint":
        if (v <= ABSOLUTE_ZERO) return ["The freezing point must be above absolute zero.", "above-absolute-zero"];
        return v < toNum(L.boilingPoint) ? null
          : ["The freezing point must be below the boiling point.", "phase-matches-temperature"];
      case "boilingPoint":
        return v > toNum(L.freezingPoint) ? null
          : ["The boiling point must be above the freezing point.", "phase-matches-temperature"];
      case "ambientTemperature": return v >= ABSOLUTE_ZERO ? null
        : ["Room temperature can't be below absolute zero.", "above-absolute-zero"];
      case "heatTransfer": return v >= 0 && v <= 1 ? null
        : ["Heat transfer must be between 0 and 1, or cooling would overshoot.", "no-overshoot"];
      default: return [`There is no law called ${e.law}.`, null];
    }
  }
  if (e.type === "spawnBody") {
    const b = e.body;
    const p = b.position.map(toNum);
    const lo = world.bounds.min.map(toNum), hi = world.bounds.max.map(toNum);
    if (p.some((x, i) => x < lo[i] || x > hi[i])) return ["New bodies must start inside the box.", "in-the-box"];
    if (toNum(b.mass) <= 0) return ["Mass must be above zero.", "positive-mass"];
    if (toNum(b.temperature) < ABSOLUTE_ZERO) return ["Nothing can be colder than absolute zero.", "above-absolute-zero"];
    if (b.velocity.some(v => Math.abs(toNum(v)) > toNum(L.maxSpeed)))
      return ["New bodies can't start faster than light.", "speed-limit"];
    return null;
  }
  if (e.type === "removeBody" || e.type === "applyImpulse" || e.type === "setBody") {
    return world.bodies.some(b => b.id === e.id) ? null : ["There is no body with that id.", null];
  }
  return null;
}

function applyEvent(world, e) {
  const w = structuredClone(world);
  switch (e.type) {
    case "setGravity": w.laws.gravity = e.value; break;
    case "reverseGravity": w.laws.gravity = w.laws.gravity.map(g => toFrac(-toNum(g))); break;
    case "disableGravity": w.laws.gravity = ["0", "0", "0"]; break;
    case "setBody": {
      const b = w.bodies.find(x => x.id === e.id);
      if (e.position) b.position = e.position;
      if (e.velocity) b.velocity = e.velocity;
      break;
    }
    case "setLaw": w.laws[e.law] = e.value; break;
    case "spawnBody": {
      const id = w.bodies.reduce((m, b) => Math.max(m, b.id + 1), 0);
      w.bodies.push({ ...e.body, id });
      break;
    }
    case "removeBody": w.bodies = w.bodies.filter(b => b.id !== e.id); break;
    case "applyImpulse": {
      const m = toNum(w.laws.maxSpeed);
      const b = w.bodies.find(x => x.id === e.id);
      b.velocity = b.velocity.map((v, i) => toFrac(clampAbs(toNum(v) + toNum(e.value[i]), m)));
      break;
    }
  }
  return w;
}

function tick(world) {
  const L = Object.fromEntries(Object.entries(world.laws).map(([k, v]) => [k, Array.isArray(v) ? v.map(toNum) : toNum(v)]));
  const lo = world.bounds.min.map(toNum), hi = world.bounds.max.map(toNum);
  const bodies = world.bodies.map(b => {
    const gas = b.phase === "gas";
    const bounce = b.phase === "liquid" ? 0 : L.restitution;
    const a = L.gravity.map(g => clampAbs(gas ? -g / 2 : g, L.maxAcceleration));
    const v = b.velocity.map((x, i) => clampAbs((toNum(x) + L.timeStep * a[i]) * (1 - L.drag), L.maxSpeed));
    const p = b.position.map((x, i) => toNum(x) + L.timeStep * v[i]);
    for (let i = 0; i < 3; i++) {
      if (p[i] < lo[i]) { p[i] = lo[i]; v[i] = -v[i] * bounce; }
      if (p[i] > hi[i]) { p[i] = hi[i]; v[i] = -v[i] * bounce; }
    }
    const t0 = toNum(b.temperature);
    const t = t0 + L.heatTransfer * (L.ambientTemperature - t0);
    return {
      ...b,
      position: p.map(x => toFrac(round(x))),
      velocity: v.map(x => toFrac(round(x))),
      temperature: toFrac(round(t)),
      phase: b.material === "water" ? phaseOf(t, L.freezingPoint, L.boilingPoint) : "solid",
    };
  });
  return { ...world, tick: world.tick + 1, bodies };
}

// The same four guarantees the Lean server tracks. The mock proves none of them.
const GUARANTEES = [
  ["positive-mass", "Every body keeps a positive mass."],
  ["in-the-box", "Every body stays inside the box."],
  ["speed-limit", "Nothing moves faster than the speed limit."],
  ["safe-environment", "The laws stay sensible."],
];

// Random law changes, like the Lean server's, but from JavaScript's own generator.
function randomEvent(seed, tick, rate) {
  const r = rng(seed * 7919 + tick + 1);
  if (r() >= rate) return null;
  const n = (lo, hi) => String(lo + Math.floor(r() * (hi - lo + 1)));
  return [
    () => ({ type: "setGravity", value: [n(-15, 15), n(-30, 10), "0"] }),
    () => ({ type: "reverseGravity" }),
    () => ({ type: "disableGravity" }),
    () => ({ type: "setLaw", law: "maxSpeed", value: n(-10, 40) }),
    () => ({ type: "setLaw", law: "maxAcceleration", value: n(-10, 60) }),
    () => ({ type: "setGravity", value: ["0", n(-30, -1), "0"] }),
  ][Math.floor(r() * 6)]();
}

/** Answers a /api/step request. */
export function step({ world, events = [], ticks = 1, randomness = "0", eventSeed = 0 }) {
  let w = world;
  const rejected = [];
  const randomEvents = [];
  events.forEach((e, index) => {
    const why = rejection(w, e);
    if (why) rejected.push({ index, event: e, reason: why[0], protects: why[1] });
    else w = applyEvent(w, e);
  });
  const frames = [];
  const rate = toNum(randomness);
  for (let i = 0; i < ticks; i++) {
    const e = randomEvent(eventSeed, w.tick, rate);
    if (e) {
      const why = rejection(w, e);
      randomEvents.push({ tick: w.tick, event: e, accepted: !why, reason: why?.[0] });
      if (!why) w = applyEvent(w, e);
    }
    w = tick(w);
    frames.push(w);
  }
  return {
    frames,
    rejected,
    randomEvents,
    guarantees: GUARANTEES.map(([id, text]) => ({
      id, text, lean: true,
      assumes: "Proved in Lean, but the mock engine is not the Lean code, so nothing here is proven.",
    })),
    engine: "mock",
  };
}

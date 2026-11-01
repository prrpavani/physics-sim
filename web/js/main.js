// Wires the controls to the engine. Every change to the world is sent as an event; the engine
// (Lean, or the mock until the server exists) decides what happens and returns the next frames.

import * as engine from "./engine.js";
import { createScene } from "./scene.js";
import { toNum, toFrac, vecNum } from "./num.js";

const $ = id => document.getElementById(id);
const TICK_MS = 1000 / 60;
const BATCH = 30;
const LOW_WATER = 20;

// ---- The laws panel ----

const LAWS = [
  { key: "gravity", label: "Gravity", unit: " m/s²", min: -5, max: 30, step: 0.1,
    hint: "Pull toward the floor. Negative pulls up.",
    get: L => -toNum(L.gravity[1]),
    event: (v, L) => ({ type: "setGravity", value: [L.gravity[0], toFrac(-v), L.gravity[2]] }) },
  { key: "wind", label: "Wind", unit: " m/s²", min: -10, max: 10, step: 0.1,
    hint: "A sideways pull.",
    get: L => toNum(L.gravity[0]),
    event: (v, L) => ({ type: "setGravity", value: [toFrac(v), L.gravity[1], L.gravity[2]] }) },
  { key: "maxSpeed", label: "Speed of light", unit: " m/s", min: -5, max: 60, step: 0.5,
    hint: "Nothing may move faster than this. Zero or below is not allowed." },
  { key: "maxAcceleration", label: "Max force", unit: " m/s²", min: -5, max: 100, step: 1,
    hint: "Caps how hard gravity can pull. Below zero is not allowed." },
  { key: "timeStep", label: "Time speed", unit: "×", min: 0, max: 3, step: 0.05,
    hint: "How much time passes each tick.",
    get: L => toNum(L.timeStep) * 60,
    value: v => toFrac(v / 60, 1200) },
  { key: "restitution", label: "Bounciness", unit: "", min: 0, max: 1.5, step: 0.05,
    hint: "Share of speed kept after hitting a wall. Above 1 is not allowed." },
  { key: "drag", label: "Air friction", unit: "", min: 0, max: 0.1, step: 0.001,
    hint: "Speed lost to the air each tick." },
  { key: "freezingPoint", label: "Freezing point", unit: " °C", min: -100, max: 150, step: 1,
    hint: "Water colder than this is ice." },
  { key: "boilingPoint", label: "Boiling point", unit: " °C", min: -50, max: 250, step: 1,
    hint: "Water this hot or hotter is steam." },
  { key: "ambientTemperature", label: "Room temperature", unit: " °C", min: -300, max: 200, step: 1,
    hint: "Everything warms or cools toward this." },
  { key: "heatTransfer", label: "Heat transfer", unit: "", min: 0, max: 0.1, step: 0.001,
    hint: "How fast bodies reach room temperature." },
];
for (const law of LAWS) {
  law.get ??= L => toNum(L[law.key]);
  law.event ??= v => ({ type: "setLaw", law: law.key, value: (law.value ?? (x => toFrac(x)))(v) });
}
// The laws the Lean model has. The others exist only in the mock engine for now.
const LEAN_LAWS = new Set(["gravity", "wind", "maxSpeed", "maxAcceleration", "restitution"]);
const lawByKey = Object.fromEntries(LAWS.map(l => [l.key, l]));

const fmt = (x, step) => {
  const digits = step >= 1 ? 0 : step >= 0.1 ? 1 : step >= 0.01 ? 2 : 3;
  return x.toFixed(digits);
};

function buildLaws() {
  const root = $("laws");
  for (const law of LAWS) {
    const div = document.createElement("div");
    div.className = "law";
    div.innerHTML = `
      <div class="law-head"><label for="law-${law.key}">${law.label}</label><output></output></div>
      <input type="range" id="law-${law.key}" min="${law.min}" max="${law.max}" step="${law.step}">
      <small>${law.hint}</small>`;
    root.append(div);
    law.div = div;
    law.input = div.querySelector("input");
    law.output = div.querySelector("output");
    let timer = 0;
    const send = () => {
      clearTimeout(timer);
      const v = Number(law.input.value);
      if (law.sent === v) return;
      law.sent = v;
      sendEvent(law.event(v, state.base.laws), law.key);
    };
    law.input.addEventListener("input", () => {
      law.output.textContent = fmt(Number(law.input.value), law.step) + law.unit;
      clearTimeout(timer);
      timer = setTimeout(send, 90);
    });
    law.input.addEventListener("change", send);
  }
}

function syncLaws(L, force = false) {
  for (const law of LAWS) {
    if (!force && document.activeElement === law.input) continue;
    const v = law.get(L);
    law.input.value = v;
    law.sent = v;
    law.output.textContent = fmt(v, law.step) + law.unit;
  }
}

// ---- Engine and playback ----

const state = {
  seed: 1, base: null, queue: [], pending: [], gen: 0, inflightGen: null,
  playing: true, acc: 0, selected: null, guaranteesKey: "",
  mode: "unprotected", protect: new Set(["positive-mass", "in-the-box", "speed-limit", "safe-environment"]),
  randomness: 0, eventSeed: 1, playback: 1,
  history: [], replay: null, openProof: null, info: [],
};

// Frames computed under old settings are no longer valid: drop them and ask again.
function invalidate() {
  state.queue = [];
  state.acc = 0;
  state.gen++;
  fill();
}

function sendEvent(event, lawKey = null) {
  state.pending.push({ event, lawKey });
  state.queue = [];   // frames computed under the old rules are no longer valid
  state.acc = 0;
  state.gen++;
  fill();
}

async function fill() {
  const gen = state.gen;
  if (!state.base || state.inflightGen === gen) return;
  if (state.queue.length >= LOW_WATER && !state.pending.length) return;
  state.inflightGen = gen;
  const from = state.queue.at(-1) || state.base;
  const sent = state.pending.slice();
  try {
    const resp = await engine.step({
      world: from, events: sent.map(p => p.event), ticks: BATCH,
      mode: state.mode, selected: [...state.protect],
      randomness: toFrac(state.randomness), eventSeed: state.eventSeed,
      proof: from._proof,
    });
    if (gen !== state.gen) return;
    state.pending.splice(0, sent.length);
    state.queue.push(...resp.frames);
    handleResponse(resp, sent);
  } catch (err) {
    toast(`Something went wrong: ${err.message}`, true);
    console.error(err);
  } finally {
    if (state.inflightGen === gen) state.inflightGen = null;
  }
}

function handleResponse(resp, sent) {
  setBadge(resp.engine);
  state.info = resp.guarantees;
  state.engine = resp.engine;
  // In the Lean engine, laws the model doesn't have can't change. Say so on the slider.
  for (const law of LAWS) law.div.classList.toggle("unmodeled", resp.engine === "lean" && !LEAN_LAWS.has(law.key));
  state.guaranteesKey = "";
  for (const r of resp.randomEvents ?? []) {
    const text = `Random: ${describe(r.event)}`;
    log(r.accepted ? text : `${text}: rejected. ${r.reason}`, r.accepted ? "event" : false);
  }
  const rejected = new Set(resp.rejected.map(r => r.index));
  for (const r of resp.rejected) {
    const p = sent[r.index];
    toast(`Rejected: ${r.reason}`, true);
    log(`${describe(p.event)}: ${r.reason}`, false);
    flashGuarantee(r.protects);
    if (p.lawKey) flashLaw(lawByKey[p.lawKey]);
  }
  sent.forEach((p, i) => { if (!rejected.has(i)) log(describe(p.event), true); });
  if (resp.frames.length) syncLaws(resp.frames[0].laws, resp.rejected.length > 0);
}

async function openUniverse(seed) {
  state.gen++;
  state.seed = seed;
  state.pending = [];
  state.queue = [];
  state.history = [];
  state.replay = null;
  $("replayBar").hidden = true;
  state.selected = null;
  scene.select(null);
  location.hash = String(seed);
  $("seed").value = seed;
  state.base = await engine.newWorld(seed);
  scene.setBounds(state.base.bounds);
  scene.clearTrails();
  syncLaws(state.base.laws, true);
  $("log").replaceChildren();
  log(`Opened universe #${seed}`, true);
  fill();
}

// ---- Bodies ----

const TEMPLATES = {
  ice: { material: "water", temperature: -15, mass: 1, name: "ice cube" },
  water: { material: "water", temperature: 20, mass: 1, name: "water drop" },
  steam: { material: "water", temperature: 110, mass: 1, name: "steam puff" },
  rubber: { material: "rubber", temperature: 20, mass: 2, name: "rubber ball" },
};

function spawn(kind) {
  const t = TEMPLATES[kind];
  const L = state.base.laws;
  const phase = t.material === "rubber" ? "solid"
    : t.temperature < toNum(L.freezingPoint) ? "solid"
    : t.temperature < toNum(L.boilingPoint) ? "liquid" : "gas";
  const r = () => Math.random() * 2 - 1;
  sendEvent({
    type: "spawnBody",
    name: t.name,
    body: {
      material: t.material, phase,
      position: [toFrac(r() * 6), "12", toFrac(r() * 6)],
      velocity: [toFrac(r() * 2), "0", toFrac(r() * 2)],
      mass: String(t.mass), temperature: String(t.temperature),
    },
  });
}

function describe(e) {
  switch (e.type) {
    case "setLaw": {
      const law = lawByKey[e.law];
      return `${law.label} → ${fmt(law.get({ [e.law]: e.value }), law.step)}${law.unit}`;
    }
    case "setGravity": return `Gravity → (${vecNum(e.value).map(x => x.toFixed(1)).join(", ")})`;
    case "reverseGravity": return "Gravity reversed";
    case "disableGravity": return "Gravity off";
    case "idle": return "Nothing";
    case "setBody": return `Edited body ${e.id}`;
    case "spawnBody": return `Added a ${e.name ?? "body"}`;
    case "removeBody": return `Removed body ${e.id}`;
    case "applyImpulse": return `Pushed body ${e.id}`;
    default: return e.type;
  }
}

function renderInspector() {
  const body = state.base?.bodies.find(b => b.id === state.selected);
  if (!body && state.selected !== null) { state.selected = null; scene.select(null); }
  $("inspectEmpty").hidden = !!body;
  $("inspectBody").hidden = !body;
  if (!body) return;
  const v = vecNum(body.velocity);
  const p = vecNum(body.position);
  const rows = [
    ["Body", `#${body.id}`],
    ["Material", body.material],
    ["Phase", body.material === "rubber" ? "solid" : { solid: "ice", liquid: "water", gas: "steam" }[body.phase]],
    ["Temperature", `${toNum(body.temperature).toFixed(1)} °C`],
    ["Mass", toNum(body.mass).toFixed(2)],
    ["Speed", `${Math.hypot(...v).toFixed(2)} m/s`],
    ["Position", p.map(x => x.toFixed(1)).join(", ")],
  ];
  $("inspectList").innerHTML = rows.map(([k, x]) => `<dt>${k}</dt><dd>${x}</dd>`).join("");
  if (!$("editBody").contains(document.activeElement)) {
    for (const input of $("editBody").querySelectorAll("input")) {
      input.value = vecNum(body[input.dataset.k])[input.dataset.i].toFixed(2);
    }
  }
}

// ---- Guarantees, badge, log, toast ----

const MARKS = { proven: "✓", violated: "✗", unknown: "?" };

// Guarantees the browser shows but the Lean model can't state yet. Always unknown.
const PLANNED = [
  ["phase-matches-temperature", "Ice is never above the freezing point, and steam is never below the boiling point."],
  ["above-absolute-zero", "Nothing gets colder than absolute zero."],
  ["no-overshoot", "Cooling never carries a body past room temperature."],
  ["bounce-no-speedup", "Hitting a wall never makes a body faster."],
].map(([id, text]) => ({
  id, text, planned: true,
  explanation: "The Lean model has no temperature, phases or bouncing yet, so this can't be stated, let alone proved.",
}));

const escape = t => String(t ?? "").replace(/[&<>"]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c]);

/** The proof panel, from the guarantee details and the status in the frame on screen. */
function renderProofs() {
  const frame = state.replay ? state.replay.frames[state.replay.i] : state.base;
  const proof = frame?._proof ?? {};
  const known = new Set(state.info.map(g => g.id));
  const list = [...state.info, ...PLANNED.filter(g => !known.has(g.id))];
  const key = JSON.stringify([proof, state.info, state.openProof, [...state.protect], state.mode, state.engine]);
  if (key === state.guaranteesKey) return;
  state.guaranteesKey = key;
  $("guarantees").innerHTML = list.map(g => {
    const track = proof[g.id];
    const status = track?.status ?? "unknown";
    const open = state.openProof === g.id;
    const why = g.planned ? "Not in the Lean model yet."
      : state.engine !== "lean" ? "Mock engine: nothing is proven."
      : track?.note ?? "";
    const checkbox = g.planned ? `<span></span>`
      : `<input type="checkbox" data-protect="${g.id}" ${state.protect.has(g.id) ? "checked" : ""} title="Protect this guarantee in Protected mode">`;
    const canReplay = status === "violated" && track.violatedAt != null &&
      state.history.some(f => f.tick === track.violatedAt);
    const detail = !open ? "" : `
      <div class="detail">
        <dl>
          ${g.statement ? `<dt>Statement</dt><dd><code>${escape(g.statement)}</code></dd>` : ""}
          ${g.theorem ? `<dt>Theorem</dt><dd><code>${escape(g.theorem)}</code></dd>` : ""}
          ${g.assumes ? `<dt>Assumes</dt><dd>${escape(g.assumes)}</dd>` : ""}
          <dt>In plain English</dt><dd>${escape(g.explanation ?? "")}</dd>
          <dt>This run</dt><dd>${escape(why)}</dd>
        </dl>
        ${canReplay ? `<button type="button" data-replay="${g.id}">Replay the counterexample</button>` : ""}
      </div>`;
    return `
      <li data-id="${g.id}">
        ${checkbox}
        <span class="mark ${status}" title="${status}">${MARKS[status]}</span>
        <span>${escape(g.text)}<span class="status ${status}">${status}</span></span>
        <small>${escape(why)}</small>
        ${detail}
      </li>`;
  }).join("");
}

function flashGuarantee(id) {
  const li = id && document.querySelector(`#guarantees li[data-id="${id}"]`);
  if (!li) return;
  li.classList.add("flash");
  setTimeout(() => li.classList.remove("flash"), 1600);
}

function flashLaw(law) {
  if (!law) return;
  law.div.classList.add("rejected");
  setTimeout(() => law.div.classList.remove("rejected"), 1600);
}

function setBadge(kind) {
  const badge = $("engineBadge");
  badge.className = `badge ${kind}`;
  badge.textContent = kind === "lean" ? "Lean engine · verified rules" : "Mock engine · nothing verified yet";
  badge.title = kind === "lean"
    ? "Every frame comes from the Lean step function the theorems are about."
    : "The Lean server is not running. A JavaScript stand-in is answering; its results are not verified.";
}

function log(text, ok) {
  const li = document.createElement("li");
  li.className = ok === "event" ? "event" : ok ? "ok" : "bad";
  li.textContent = `${state.base ? `t${state.base.tick} ` : ""}${text}`;
  $("log").prepend(li);
  while ($("log").children.length > 40) $("log").lastChild.remove();
}

let toastTimer = 0;
function toast(text, bad = false) {
  const el = $("toast");
  el.textContent = text;
  el.className = bad ? "bad" : "";
  el.hidden = false;
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => { el.hidden = true; }, 3200);
}

// ---- Main loop ----

const scene = createScene($("view"));
let last = performance.now();
let uiCounter = 0;

function frame(now) {
  requestAnimationFrame(frame);
  const elapsed = Math.min(now - last, 100);
  last = now;
  if (!state.base) return;
  if (state.replay) {
    replayFrame(elapsed);
  } else {
    if (state.playing && state.queue.length) {
      state.acc += elapsed * state.playback;
      while (state.acc >= TICK_MS && state.queue.length) advance();
      if (!state.queue.length) state.acc = 0;
    }
    const next = state.queue[0] ?? state.base;
    scene.show(state.base, next, state.queue.length ? state.acc / TICK_MS : 0);
  }
  renderProofs();
  scene.render();
  if (++uiCounter % 6 === 0) {
    $("tick").textContent = state.base.tick;
    $("count").textContent = state.base.bodies.length;
    renderInspector();
  }
  fill();
}

// ---- Controls ----

buildLaws();

document.querySelectorAll("[data-spawn]").forEach(b =>
  b.addEventListener("click", () => spawn(b.dataset.spawn)));

$("play").addEventListener("click", () => {
  state.playing = !state.playing;
  $("play").textContent = state.playing ? "Pause" : "Play";
});
$("stepOnce").addEventListener("click", () => {
  state.playing = false;
  $("play").textContent = "Play";
  if (state.queue.length) { advance(); state.acc = 0; }
});
$("reset").addEventListener("click", () => openUniverse(state.seed));
$("seedForm").addEventListener("submit", e => {
  e.preventDefault();
  openUniverse(Math.max(0, Math.floor(Number($("seed").value) || 0)));
});
$("randomSeed").addEventListener("click", () => openUniverse(Math.floor(Math.random() * 1e6)));

$("pushBody").addEventListener("click", () => {
  if (state.selected === null) return;
  const r = () => Math.random() * 4 - 2;
  sendEvent({ type: "applyImpulse", id: state.selected, value: [toFrac(r()), "10", toFrac(r())] });
});
$("removeBody").addEventListener("click", () => {
  if (state.selected !== null) sendEvent({ type: "removeBody", id: state.selected });
});

// A click (not a drag) selects the body under the pointer.
let down = null;
$("view").addEventListener("pointerdown", e => { down = [e.clientX, e.clientY]; });
$("view").addEventListener("pointerup", e => {
  if (!down || Math.hypot(e.clientX - down[0], e.clientY - down[1]) > 5) return;
  state.selected = scene.pick(e.clientX, e.clientY);
  scene.select(state.selected);
  renderInspector();
});

// ---- Added: history and replay ----

const HISTORY = 6000;

/** Show the next frame, and remember it for replays. */
function advance() {
  state.base = state.queue.shift();
  state.acc -= TICK_MS;
  state.history.push(state.base);
  if (state.history.length > HISTORY) state.history.shift();
}

/** Replay the run that broke a guarantee: from where its proof started to just after it failed. */
function startReplay(id) {
  const track = state.base?._proof?.[id];
  if (!track) return;
  const frames = state.history.filter(f => f.tick >= track.since && f.tick <= track.violatedAt + 30);
  if (!frames.length) return;
  state.replay = { frames, i: 0, acc: 0, until: track.violatedAt, id };
  scene.clearTrails();
  $("replayBar").hidden = false;
}

function replayFrame(elapsed) {
  const r = state.replay;
  r.acc += elapsed * state.playback * (r.frames[r.i].tick >= r.until - 5 ? 0.25 : 1);
  while (r.acc >= TICK_MS && r.i < r.frames.length - 1) { r.i++; r.acc -= TICK_MS; }
  const f = r.frames[r.i];
  const g = state.info.find(x => x.id === r.id);
  $("replayText").textContent = f.tick >= r.until
    ? `Tick ${f.tick}: "${g?.text}" is broken here.`
    : `Replaying tick ${f.tick} of ${r.until}…`;
  scene.show(f, r.frames[Math.min(r.i + 1, r.frames.length - 1)], r.acc / TICK_MS);
  if (r.i === r.frames.length - 1) r.acc = 0;
}

$("replayExit").addEventListener("click", () => {
  state.replay = null;
  $("replayBar").hidden = true;
  scene.clearTrails();
});

// ---- Added: proof panel clicks ----

$("guarantees").addEventListener("click", e => {
  const box = e.target.closest("[data-protect]");
  if (box) {
    if (box.checked) state.protect.add(box.dataset.protect); else state.protect.delete(box.dataset.protect);
    invalidate();
    return;
  }
  const replay = e.target.closest("[data-replay]");
  if (replay) { startReplay(replay.dataset.replay); return; }
  if (e.target.closest(".detail")) return;
  const li = e.target.closest("li");
  if (li) { state.openProof = state.openProof === li.dataset.id ? null : li.dataset.id; state.guaranteesKey = ""; }
});

// ---- Added: protected / unprotected mode ----

function setMode(mode) {
  state.mode = mode;
  document.querySelectorAll("[data-mode]").forEach(b => b.classList.toggle("on", b.dataset.mode === mode));
  invalidate();
}
document.querySelectorAll("[data-mode]").forEach(b => b.addEventListener("click", () => setMode(b.dataset.mode)));

// ---- Added: chaos ----

function setRandomness(v) {
  state.randomness = v;
  $("randomness").value = v;
  $("randomnessOut").textContent = v === 0 ? "off" : `${(v * 100).toFixed(1)}% per tick`;
  invalidate();
}
$("randomness").addEventListener("input", () => setRandomness(Number($("randomness").value)));
$("eventSeed").addEventListener("change", () => {
  state.eventSeed = Math.max(0, Math.floor(Number($("eventSeed").value) || 0));
  invalidate();
});

// ---- Added: gravity direction ----

const gravityStrength = () => Math.hypot(...vecNum(state.base.laws.gravity)) || 9.81;
$("laws").parentElement.querySelectorAll("[data-gravity]").forEach(b => b.addEventListener("click", () => {
  const g = toFrac(gravityStrength());
  const neg = toFrac(-gravityStrength());
  const events = {
    down: { type: "setGravity", value: ["0", neg, "0"] },
    up: { type: "setGravity", value: ["0", g, "0"] },
    side: { type: "setGravity", value: [g, "0", "0"] },
    reverse: { type: "reverseGravity" },
    off: { type: "disableGravity" },
  };
  sendEvent(events[b.dataset.gravity]);
}));

// ---- Added: presets ----

const PRESETS = [
  ["Normal", { events: [
    { type: "setLaw", law: "maxAcceleration", value: "40" },
    { type: "setLaw", law: "maxSpeed", value: "30" },
    { type: "setGravity", value: ["0", "-981/100", "0"] }], randomness: 0 }],
  ["Low gravity", { events: [{ type: "setGravity", value: ["0", "-81/50", "0"] }] }],
  ["Zero gravity", { events: [{ type: "disableGravity" }] }],
  ["Strong gravity", { events: [
    { type: "setLaw", law: "maxAcceleration", value: "80" },
    { type: "setGravity", value: ["0", "-60", "0"] }] }],
  ["Chaotic", { events: [], randomness: 0.05, mode: "unprotected" }],
  ["Protected", { events: [], randomness: 0.05, mode: "protected",
    protect: ["positive-mass", "in-the-box", "speed-limit", "safe-environment"] }],
];
for (const [name, preset] of PRESETS) {
  const b = document.createElement("button");
  b.type = "button";
  b.textContent = name;
  b.addEventListener("click", () => {
    if (preset.protect) state.protect = new Set(preset.protect);
    if (preset.mode) setMode(preset.mode);
    if (preset.randomness !== undefined) setRandomness(preset.randomness);
    for (const e of preset.events) sendEvent(e);
    log(`Preset: ${name}`, true);
  });
  $("presets").append(b);
}

// ---- Added: editing a body ----

$("editBody").addEventListener("submit", e => {
  e.preventDefault();
  if (state.selected === null) return;
  const read = k => [0, 1, 2].map(i =>
    toFrac(Number($("editBody").querySelector(`[data-k="${k}"][data-i="${i}"]`).value) || 0));
  sendEvent({ type: "setBody", id: state.selected, position: read("position"), velocity: read("velocity") });
  document.activeElement.blur();
});
$("speed1000").addEventListener("click", () => {
  const body = state.base?.bodies.find(b => b.id === state.selected);
  if (!body) return;
  sendEvent({ type: "setBody", id: body.id, velocity: vecNum(body.velocity).map(v => toFrac(v * 1000)) });
});

// ---- Added: playback speed (drawing only; the model's time step is a law) ----

$("playback").addEventListener("input", () => {
  state.playback = Number($("playback").value);
  $("playbackOut").textContent = `${state.playback}×`;
});

setMode("unprotected");
setRandomness(0);

openUniverse(Number(location.hash.slice(1)) || Math.floor(Math.random() * 1e6)).catch(err => toast(err.message, true));
requestAnimationFrame(frame);

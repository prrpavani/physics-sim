import { useStore } from "../store";
import { frac, num, vec } from "../lib/num";
import { LawSlider, Select } from "./common";
import type { CollisionMode, LawExpr, Metric, Topology } from "../../../../shared/types/paradox";

const constOf = (e: LawExpr): number => (e.type === "const" ? num(e.value) : 0);

const COLLISIONS: { value: CollisionMode; label: string }[] = [
  { value: "none", label: "Pass through" },
  { value: "bounce", label: "Bounce" },
  { value: "exchangeVelocity", label: "Swap velocities" },
  { value: "exchangeMass", label: "Swap masses" },
  { value: "merge", label: "Merge into one" },
  { value: "spawn", label: "Create a new object" },
];

export function LawsTab() {
  const laws = useStore(s => s.world?.laws);
  const send = useStore(s => s.send);
  if (!laws) return null;
  const g = [num(laws.gravity.x), num(laws.gravity.y), num(laws.gravity.z)];
  const setG = (i: number, v: number) => {
    const next = [...g]; next[i] = v;
    send({ type: "changeGravity", gravity: vec(next[0], next[1], next[2]) });
  };
  return (
    <div className="tab">
      <h2>Fundamental laws</h2>
      <p className="lede">Move a slider and the universe changes in the next few steps. In protected mode, unsafe values are repaired or refused.</p>

      <h3>Gravity</h3>
      <LawSlider label="Up and down" value={g[1]} min={-60} max={60} step={0.5} unit=" m/s²" onCommit={v => setG(1, v)} hint="Positive pulls up." />
      <LawSlider label="Sideways" value={g[0]} min={-60} max={60} step={0.5} unit=" m/s²" onCommit={v => setG(0, v)} />
      <LawSlider label="Forward and back" value={g[2]} min={-60} max={60} step={0.5} unit=" m/s²" onCommit={v => setG(2, v)} />
      <div className="row">
        <button type="button" onClick={() => send({ type: "reverseGravity" })}>Reverse</button>
        <button type="button" onClick={() => send({ type: "disableGravity" })}>Switch off</button>
      </div>

      <h3>Limits</h3>
      <LawSlider label="Speed limit" value={num(laws.maxSpeed)} min={-5} max={80} step={0.5} unit=" m/s"
        onCommit={v => send({ type: "changeMaxSpeed", value: frac(v) })}
        danger={v => (v <= 0 ? "Not a meaningful limit. Protected mode refuses this." : null)} />
      <LawSlider label="Acceleration limit" value={num(laws.maxAcceleration)} min={-5} max={200} step={1} unit=" m/s²"
        onCommit={v => send({ type: "changeMaxAcceleration", value: frac(v) })}
        danger={v => (v < 0 ? "Below zero. Protected mode repairs this to 0." : null)} />

      <h3>Collisions and walls</h3>
      <div className="field">
        <label>When objects touch</label>
        <Select label="When objects touch" value={laws.collisions} options={COLLISIONS}
          onChange={mode => send({ type: "setCollisions", mode })} />
      </div>
      <LawSlider label="Bounciness" value={num(laws.restitution)} min={0} max={2} step={0.05}
        onCommit={v => send({ type: "changeRestitution", value: frac(v) })}
        danger={v => (v > 1 ? "Walls would add speed. Protected mode repairs this to 1." : null)} />

      <h3>Other forces</h3>
      <LawSlider label="Drag" value={constOf(laws.drag)} min={-1} max={2} step={0.05}
        onCommit={v => send({ type: "setDrag", formula: { type: "const", value: frac(v) } })}
        hint="Negative drag speeds objects up on their own." />
      <LawSlider label="Pull toward the centre" value={constOf(laws.central)} min={-2} max={2} step={0.05}
        onCommit={v => send({ type: "setCentral", formula: { type: "const", value: frac(v) } })}
        hint="Negative pushes everything outward." />
      <LawSlider label="Magnetic field" value={num(laws.magnetic.y)} min={-5} max={5} step={0.1}
        onCommit={v => send({ type: "setMagnetic", field: vec(0, v, 0) })}
        hint="Turns moving charged objects." />

      <h3>Mass and time</h3>
      <LawSlider label="Mass change per step" value={num(laws.massRate)} min={-0.5} max={1.1} step={0.001}
        onCommit={v => send({ type: "setMassRate", value: frac(v) })}
        danger={v => (v <= 0 ? "Mass would stop being positive. Protected mode refuses this." : null)} hint="1 keeps mass the same." />
      <LawSlider label="Time step" value={num(laws.timeStep)} min={0.002} max={0.1} step={0.002} unit=" s"
        onCommit={v => send({ type: "changeTimeStep", value: frac(v) })} />
      <button type="button" onClick={() => send({ type: "reverseTime" })}>Reverse time</button>

      <h3>Space</h3>
      <div className="field">
        <label>Shape of space</label>
        <Select<Topology> label="Shape of space" value={laws.topology}
          options={[{ value: "box", label: "Solid walls" }, { value: "torus", label: "Loops around" }]}
          onChange={topology => send({ type: "setTopology", topology })} />
      </div>
      <div className="field">
        <label>How force measures distance</label>
        <Select<Metric> label="Distance" value={laws.metric}
          options={[{ value: "euclidean", label: "Straight line" }, { value: "manhattan", label: "Taxicab" }, { value: "chebyshev", label: "Longest axis" }]}
          onChange={metric => send({ type: "setMetric", metric })} />
      </div>
    </div>
  );
}

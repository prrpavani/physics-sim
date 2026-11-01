import { useEffect, useState } from "react";
import type { Body } from "../../../../shared/types/paradox";
import { clock, useStore } from "../store";
import { num, showNum, vec, vecNums } from "../lib/num";
import { NumberInput } from "./common";

const KINDS: { name: string; about: string; make: () => Partial<Body> }[] = [
  { name: "Sphere", about: "Mass 1, no charge", make: () => ({ shape: { type: "sphere", radius: "1/2" }, mass: "1", charge: "0" }) },
  { name: "Cube", about: "Mass 2, no charge", make: () => ({ shape: { type: "cube", halfWidth: "3/5" }, mass: "2", charge: "0" }) },
  { name: "Planet", about: "Large and heavy", make: () => ({ shape: { type: "sphere", radius: "3/2" }, mass: "40", charge: "0" }) },
  { name: "Positive", about: "Charge +1", make: () => ({ shape: { type: "sphere", radius: "2/5" }, mass: "1", charge: "1" }) },
  { name: "Negative", about: "Charge −1", make: () => ({ shape: { type: "sphere", radius: "2/5" }, mass: "1", charge: "-1" }) },
  { name: "No mass", about: "Invalid. Protected mode refuses it.", make: () => ({ shape: { type: "sphere", radius: "1/2" }, mass: "0", charge: "0" }) },
];

function Inspect({ id }: { id: number }) {
  const send = useStore(s => s.send);
  const select = useStore(s => s.select);
  const tick = useStore(s => s.tick);
  const world = useStore(s => s.world);
  void tick;
  const body = clock.current?.bodies.find(b => b.id === id);
  const [pos, setPos] = useState<string[]>(["0", "0", "0"]);
  const [velDraft, setVelDraft] = useState<string[]>(["0", "0", "0"]);
  useEffect(() => {
    if (!body) return;
    setPos(vecNums(body.position).map(v => v.toFixed(1)));
    setVelDraft(vecNums(body.velocity).map(v => v.toFixed(1)));
  }, [id]);
  if (!body) return <p className="muted">This object no longer exists.</p>;
  const limit = world ? num(world.laws.maxSpeed) : 0;
  const v = vecNums(body.velocity);
  const fastest = Math.max(...v.map(Math.abs));

  return (
    <div className="inspect">
      <div className="inspect-head">
        <strong>Object {id}</strong>
        <button type="button" className="icon" aria-label="Clear selection" onClick={() => select(null)}>×</button>
      </div>
      <dl>
        <dt>Mass</dt><dd title={body.mass}>{showNum(body.mass, 3)}</dd>
        <dt>Charge</dt><dd>{showNum(body.charge)}</dd>
        <dt>Exact x</dt><dd className="exact">{body.position.x}</dd>
        <dt>Velocity</dt><dd>{v.map(x => x.toFixed(2)).join(", ")}</dd>
        <dt>Speed limit</dt>
        <dd>
          <span className="meter"><span style={{ width: `${Math.min(fastest / Math.max(limit, 0.001), 1) * 100}%` }} className={fastest > limit ? "over" : ""} /></span>
        </dd>
      </dl>
      <div className="vec-edit"><label>Position</label>
        {pos.map((p, i) => <NumberInput key={i} label={`Position ${"xyz"[i]}`} value={p} onChange={x => setPos(pos.map((o, j) => (j === i ? x : o)))} />)}
      </div>
      <div className="vec-edit"><label>Velocity</label>
        {velDraft.map((p, i) => <NumberInput key={i} label={`Velocity ${"xyz"[i]}`} value={p} onChange={x => setVelDraft(velDraft.map((o, j) => (j === i ? x : o)))} />)}
      </div>
      <div className="row">
        <button type="button" onClick={() => send({ type: "setBodyState", id, position: vec(+pos[0], +pos[1], +pos[2]), velocity: vec(+velDraft[0], +velDraft[1], +velDraft[2]) })}>Apply</button>
        <button type="button" onClick={() => send({ type: "applyImpulse", id, impulse: vec(0, 12, 0) })}>Push up</button>
        <button type="button" onClick={() => send({ type: "applyImpulse", id, impulse: vec(v[0] * 999, v[1] * 999, v[2] * 999) })}>Speed ×1000</button>
        <button type="button" className="danger" onClick={() => { send({ type: "removeBody", id }); select(null); }}>Remove</button>
      </div>
    </div>
  );
}

export function ObjectsTab() {
  const world = useStore(s => s.world);
  const send = useStore(s => s.send);
  const selected = useStore(s => s.selected);
  if (!world) return null;

  const spawn = (kind: (typeof KINDS)[number]) => {
    const r = () => Math.random() * 10 - 5;
    send({
      type: "spawnBody",
      body: {
        id: world.nextId, position: vec(r(), r(), r()), velocity: vec(r() / 2, r() / 2, r() / 2),
        shape: { type: "sphere", radius: "1/2" }, mass: "1", charge: "0", ...kind.make(),
      },
    });
  };

  return (
    <div className="tab">
      <h2>Objects</h2>
      <p className="lede">Add objects, or click one in the universe to inspect and edit it.</p>
      <div className="spawn-grid">
        {KINDS.map(k => (
          <button key={k.name} type="button" className="spawn" onClick={() => spawn(k)}>
            <strong>{k.name}</strong><span>{k.about}</span>
          </button>
        ))}
      </div>
      {selected !== null ? <Inspect key={selected} id={selected} /> : <p className="muted hint-box">Nothing selected. Click an object in the universe.</p>}
    </div>
  );
}

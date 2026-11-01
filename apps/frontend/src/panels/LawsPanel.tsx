import { useEffect, useRef, useState } from "react";
import type { Laws } from "../api";
import { frac, num } from "../lib/num";
import { useStore } from "../store";

function Slider({ label, hint, value, min, max, step, onCommit }: {
  label: string; hint: string; value: number; min: number; max: number; step: number; onCommit: (v: number) => void;
}) {
  const [local, setLocal] = useState(value);
  const active = useRef(false);
  const timer = useRef<ReturnType<typeof setTimeout>>(undefined);
  useEffect(() => { if (!active.current) setLocal(value); }, [value]);
  return (
    <div className="slider">
      <div className="slider-head"><label>{label}</label><output>{local.toFixed(step >= 1 ? 0 : step >= 0.1 ? 1 : 2)}</output></div>
      <input type="range" aria-label={label} min={min} max={max} step={step} value={local}
        onChange={e => {
          const v = Number(e.target.value);
          setLocal(v);
          active.current = true;
          clearTimeout(timer.current);
          timer.current = setTimeout(() => { active.current = false; onCommit(v); }, 140);
        }} />
      <small>{hint}</small>
    </div>
  );
}

function Toggle({ label, hint, on, onChange }: { label: string; hint: string; on: boolean; onChange: (v: boolean) => void }) {
  return (
    <label className="toggle">
      <input type="checkbox" checked={on} onChange={e => onChange(e.target.checked)} />
      <span className="track" aria-hidden />
      <span><strong>{label}</strong><small>{hint}</small></span>
    </label>
  );
}

const TRY: { name: string; laws: Partial<Laws> }[] = [
  { name: "Velocity ×100", laws: { multiplier: "100", limiter: false } },
  { name: "Bouncy walls", laws: { restitution: "2", limiter: false } },
  { name: "Third law off", laws: { gravity: "0", pull: "20", thirdLaw: false } },
  { name: "No forces", laws: { gravity: "0", pull: "0", restitution: "1", multiplier: "1", limiter: false } },
];

export function LawsPanel() {
  const laws = useStore(s => s.laws);
  const setLaws = useStore(s => s.setLaws);
  if (!laws) return null;
  return (
    <aside className="panel laws">
      <h2>Change the laws</h2>

      <div className="try-row">
        {TRY.map(t => <button key={t.name} type="button" className="chip" onClick={() => setLaws(t.laws)}>{t.name}</button>)}
      </div>

      <Slider label="Gravity" hint="Negative pulls down. Positive pulls up." value={num(laws.gravity)} min={-40} max={40} step={1}
        onCommit={v => setLaws({ gravity: frac(v) })} />

      <Slider label="Pull between objects" hint="Positive attracts. Negative repels." value={num(laws.pull)} min={-40} max={40} step={1}
        onCommit={v => setLaws({ pull: frac(v) })} />
      <Toggle label="Newton's third law" hint="Every pull is matched by a pull back." on={laws.thirdLaw}
        onChange={thirdLaw => setLaws({ thirdLaw })} />

      <Slider label="Bounciness" hint="Speed kept at a wall. Above 1, walls add speed." value={num(laws.restitution)} min={0} max={2} step={0.05}
        onCommit={v => setLaws({ restitution: frac(v) })} />

      <Slider label="Speed multiplier" hint="Multiplies every velocity, every step." value={num(laws.multiplier)} min={-3} max={100} step={0.5}
        onCommit={v => setLaws({ multiplier: frac(v) })} />
      <Toggle label="Limiter" hint={`Enforces the speed limit of ${num(laws.maxSpeed)} last in each step.`} on={laws.limiter}
        onChange={limiter => setLaws({ limiter })} />
    </aside>
  );
}

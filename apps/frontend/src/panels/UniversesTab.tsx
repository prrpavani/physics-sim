import { useState } from "react";
import { useStore } from "../store";

export function UniversesTab() {
  const presets = useStore(s => s.presets);
  const presetName = useStore(s => s.presetName);
  const open = useStore(s => s.open);
  const seed = useStore(s => s.seed);
  const [draft, setDraft] = useState(String(seed));

  return (
    <div className="tab">
      <h2>Pick a universe</h2>
      <p className="lede">Each one is a different set of laws, ready to run. Change anything afterwards.</p>
      <div className="seed-row">
        <label htmlFor="worldSeed" className="label">World seed</label>
        <input id="worldSeed" className="seed" type="number" min={0} value={draft} onChange={e => setDraft(e.target.value)} />
        <button type="button" onClick={() => void open(presetName, Number(draft) || 0)}>Open</button>
        <button type="button" className="ghost" onClick={() => {
          const s = Math.floor(Math.random() * 1_000_000);
          setDraft(String(s));
          void open(presetName, s);
        }}>Random</button>
      </div>
      <div className="preset-grid">
        {presets.map(p => (
          <button key={p.name} type="button" className={`preset ${p.name === presetName ? "on" : ""}`}
            onClick={() => void open(p.name, Number(draft) || 0)}>
            <strong>{p.title}</strong>
            <span>{p.description}</span>
          </button>
        ))}
      </div>
    </div>
  );
}

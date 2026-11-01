import { useState } from "react";
import { useStore } from "../store";

const SPEEDS = [0.25, 0.5, 1, 2, 4];

export function Transport() {
  const playing = useStore(s => s.playing);
  const setPlaying = useStore(s => s.setPlaying);
  const stepOnce = useStore(s => s.stepOnce);
  const reset = useStore(s => s.reset);
  const speed = useStore(s => s.speed);
  const setSpeed = useStore(s => s.setSpeed);
  const tick = useStore(s => s.tick);
  const bodies = useStore(s => s.world?.bodies.length ?? 0);
  const chaosRate = useStore(s => s.chaosRate);
  const chaosKind = useStore(s => s.chaosKind);
  const chaosSeed = useStore(s => s.chaosSeed);
  const setChaos = useStore(s => s.setChaos);
  const setChaosSeed = useStore(s => s.setChaosSeed);
  const log = useStore(s => s.log);
  const showVectors = useStore(s => s.showVectors);
  const showTrails = useStore(s => s.showTrails);
  const toggleVectors = useStore(s => s.toggleVectors);
  const toggleTrails = useStore(s => s.toggleTrails);
  const replaying = useStore(s => !!s.replay);
  const [historyOpen, setHistoryOpen] = useState(false);

  return (
    <footer className={`transport ${replaying ? "dimmed" : ""}`}>
      {historyOpen && (
        <div className="history" role="log">
          <h3>Experiment history</h3>
          {log.length === 0 && <p className="muted">Nothing has happened yet.</p>}
          {log.map(e => (
            <div key={e.id} className={`log-line ${e.kind}`}>
              <span className="log-tick">{e.tick}</span>
              <span className="log-mark" aria-hidden />
              <span className="log-text">{e.text}{e.detail && <small>{e.detail}</small>}</span>
            </div>
          ))}
        </div>
      )}
      <div className="transport-group">
        <button type="button" className="play" onClick={() => setPlaying(!playing)} aria-label={playing ? "Pause" : "Play"} disabled={replaying}>
          {playing ? <svg viewBox="0 0 24 24"><rect x="6" y="5" width="4" height="14" /><rect x="14" y="5" width="4" height="14" /></svg>
            : <svg viewBox="0 0 24 24"><path d="M7 4l13 8-13 8z" /></svg>}
        </button>
        <button type="button" onClick={() => stepOnce()} disabled={playing || replaying} title="Advance one step (.)">Step</button>
        <button type="button" onClick={() => void reset()} disabled={replaying}>Reset</button>
      </div>
      <div className="readout"><span className="label">Step</span><span className="value">{tick}</span></div>
      <div className="readout"><span className="label">Objects</span><span className="value">{bodies}</span></div>
      <div className="transport-group">
        <span className="label">Speed</span>
        <div className="segmented">
          {SPEEDS.map(s => (
            <button key={s} type="button" aria-pressed={speed === s} onClick={() => setSpeed(s)}>{s}×</button>
          ))}
        </div>
      </div>
      <div className="transport-group chaos">
        <label className="label" htmlFor="chaos">Chaos</label>
        <input id="chaos" type="range" min={0} max={200} step={5} value={chaosRate}
          onChange={e => setChaos(Number(e.target.value))} />
        <span className="value small">{(chaosRate / 10).toFixed(1)}%</span>
        <div className="segmented" title="Safe chaos is proved to keep every guarantee. Wild chaos may break the rules.">
          <button type="button" aria-pressed={chaosKind === "safe"} onClick={() => setChaos(chaosRate, "safe")}>Safe</button>
          <button type="button" aria-pressed={chaosKind === "wild"} onClick={() => setChaos(chaosRate, "wild")}>Wild</button>
        </div>
        <label className="label" htmlFor="chaosSeed">Seed</label>
        <input id="chaosSeed" className="seed" type="number" min={0} value={chaosSeed}
          onChange={e => setChaosSeed(Number(e.target.value) || 0)} />
      </div>
      <div className="transport-group end">
        <button type="button" className="ghost" aria-pressed={showTrails} onClick={toggleTrails}>Trails</button>
        <button type="button" className="ghost" aria-pressed={showVectors} onClick={toggleVectors}>Vectors</button>
        <button type="button" className="ghost" aria-pressed={historyOpen} onClick={() => setHistoryOpen(o => !o)}>History</button>
      </div>
    </footer>
  );
}

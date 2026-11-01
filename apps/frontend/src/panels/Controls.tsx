import { num } from "../lib/num";
import { useStore } from "../store";

const PLAY = <svg viewBox="0 0 24 24"><path d="M7 4l13 8-13 8z" /></svg>;
const PAUSE = <svg viewBox="0 0 24 24"><rect x="6" y="5" width="4" height="14" /><rect x="14" y="5" width="4" height="14" /></svg>;

export function Controls() {
  const playing = useStore(s => s.playing);
  const setPlaying = useStore(s => s.setPlaying);
  const stepOnce = useStore(s => s.stepOnce);
  const reset = useStore(s => s.reset);
  const tick = useStore(s => s.tick);
  return (
    <div className="controls">
      <button type="button" className="play" onClick={() => setPlaying(!playing)} aria-label={playing ? "Pause" : "Play"}>{playing ? PAUSE : PLAY}</button>
      <button type="button" onClick={stepOnce} disabled={playing}>Step</button>
      <button type="button" onClick={() => void reset()}>Start over</button>
      <span className="tick">Step {tick}</span>
    </div>
  );
}

export function ReplayBar() {
  const replay = useStore(s => s.replay);
  const setIndex = useStore(s => s.setReplayIndex);
  const toggle = useStore(s => s.toggleReplay);
  const exit = useStore(s => s.exitReplay);
  if (!replay) return null;
  const total = replay.trace.states.length;
  const shown = replay.index === 0 ? replay.trace.start : replay.trace.states[replay.index - 1];
  const fastest = Math.max(...shown.bodies.flatMap(b => (b.drawVelocity ?? [0, 0, 0]).map(Math.abs)));
  return (
    <div className="replay" role="region" aria-label="Counterexample replay">
      <div className="replay-head">
        <span className="replay-tag">Counterexample</span>
        <strong>{replay.title}</strong>
        <button type="button" onClick={exit}>Back to live</button>
      </div>
      <p>Lean replayed this run through the real step function and confirmed it breaks the promise.{replay.fromProbe ? " It starts from a small test universe under the same laws." : ""}</p>
      {replay.title === "Speed limit" && (
        <p className="replay-numbers">Fastest velocity {fastest.toLocaleString()}. Limit {num(shown.laws.maxSpeed)}.</p>
      )}
      <div className="replay-track">
        <button type="button" className="play small" onClick={toggle} aria-label={replay.playing ? "Pause replay" : "Play replay"}>{replay.playing ? PAUSE : PLAY}</button>
        <input type="range" min={0} max={total} value={replay.index} onChange={e => setIndex(Number(e.target.value))} aria-label="Replay position" />
        <span className="tick">{replay.index} / {total}</span>
      </div>
    </div>
  );
}

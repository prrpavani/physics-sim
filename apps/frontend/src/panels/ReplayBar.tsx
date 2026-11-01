import { useStore } from "../store";
import * as pretty from "../lib/pretty";

export function ReplayBar() {
  const replay = useStore(s => s.replay);
  const setIndex = useStore(s => s.setReplayIndex);
  const toggle = useStore(s => s.toggleReplayPlaying);
  const exit = useStore(s => s.exitReplay);
  if (!replay) return null;
  const { trace, index, checked, claim, scope } = replay;
  const total = trace.states.length;
  const currentEvent = index === 0 ? null : trace.events[index - 1];
  return (
    <div className="replay-bar" role="region" aria-label="Counterexample replay">
      <div className="replay-head">
        <span className="replay-tag">Counterexample</span>
        <strong>{pretty.claim(claim)}</strong>
        <span className={`check-chip ${checked ? (checked.valid ? "ok" : "bad") : ""}`}>
          {!checked ? "Lean is checking this run…" : checked.valid
            ? "Lean replayed this run and confirmed it breaks the claim"
            : "This trace did not pass the check"}
        </span>
        <span className="muted scope-note">
          {scope === "allowed" ? "Using only permitted events" : scope === "timeOnly" ? "No events: time alone" : "Using events a protected universe would refuse"}
        </span>
        <button type="button" className="ghost" onClick={exit}>Back to live</button>
      </div>
      <div className="replay-track">
        <button type="button" onClick={toggle} className="play small" aria-label={replay.playing ? "Pause replay" : "Play replay"}>
          {replay.playing ? <svg viewBox="0 0 24 24"><rect x="6" y="5" width="4" height="14" /><rect x="14" y="5" width="4" height="14" /></svg>
            : <svg viewBox="0 0 24 24"><path d="M7 4l13 8-13 8z" /></svg>}
        </button>
        <input type="range" min={0} max={total} value={index} onChange={e => setIndex(Number(e.target.value))} aria-label="Replay position" />
        <span className="replay-pos">{index} / {total}</span>
        <span className="replay-event">{index === 0 ? "The starting state" : index === total ? `${pretty.event(currentEvent!)}. The claim is now broken.` : pretty.event(currentEvent!)}</span>
      </div>
    </div>
  );
}

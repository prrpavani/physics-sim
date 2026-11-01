import { useStore } from "../store";

export function TopBar({ onTour }: { onTour: () => void }) {
  const mode = useStore(s => s.mode);
  const setMode = useStore(s => s.setMode);
  const presets = useStore(s => s.presets);
  const presetName = useStore(s => s.presetName);
  const title = presets.find(p => p.name === presetName)?.title ?? "";

  return (
    <header className="topbar">
      <div className="brand">
        <span className="wordmark">PARADOX</span>
        <span className="tagline">{title || "Build a universe. Change its laws. Prove it makes sense."}</span>
      </div>
      <div className={`mode-switch ${mode}`} role="group" aria-label="Universe mode">
        <button type="button" aria-pressed={mode === "protected"} onClick={() => setMode("protected")}
          title="Every change must keep every guarantee. Unsafe changes are repaired or rejected.">
          <span className="dot" /> Protected
        </button>
        <button type="button" aria-pressed={mode === "unprotected"} onClick={() => setMode("unprotected")}
          title="Anything goes. Lean computes what happens and reports what breaks.">
          <span className="dot" /> Unprotected
        </button>
      </div>
      <div className="top-actions">
        <button type="button" className="ghost" onClick={onTour}>Guided demo</button>
        <span className="engine-chip" title="Every state on screen is computed by the Lean formal model, in exact rationals.">
          <span className="pulse" /> Lean 4 model
        </span>
      </div>
    </header>
  );
}

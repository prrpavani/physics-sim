import { useEffect } from "react";
import { Universe } from "./scene/Universe";
import { useStore } from "./store";
import { LawsPanel } from "./panels/LawsPanel";
import { ProofPanel } from "./panels/ProofPanel";
import { Controls, ReplayBar } from "./panels/Controls";

export function App() {
  const init = useStore(s => s.init);
  const error = useStore(s => s.error);
  const notice = useStore(s => s.notice);
  const locked = useStore(s => s.locked);
  const setLocked = useStore(s => s.setLocked);

  useEffect(() => { void init(); }, [init]);

  useEffect(() => {
    const onKey = (e: KeyboardEvent) => {
      if ((e.target as HTMLElement).tagName === "INPUT") return;
      if (e.code === "Space") { e.preventDefault(); const s = useStore.getState(); s.setPlaying(!s.playing); }
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, []);

  return (
    <div className="app">
      <div className="viewport"><Universe /></div>
      <header className="topbar">
        <div className="brand"><span className="wordmark">PARADOX</span><span className="tagline">Change the laws of a universe. See what Lean can prove.</span></div>
        <label className={`lock ${locked ? "on" : ""}`} title="When on, changes that could break the speed limit are repaired. When off, anything goes.">
          <input type="checkbox" checked={locked} onChange={e => setLocked(e.target.checked)} />
          <span className="track" aria-hidden />
          Keep it consistent
        </label>
      </header>
      <LawsPanel />
      <ProofPanel />
      <Controls />
      <ReplayBar />
      {notice && <div className="notice" role="status">{notice}</div>}
      {error && <div className="fatal" role="alert"><strong>There is a problem</strong><span>{error}</span></div>}
    </div>
  );
}

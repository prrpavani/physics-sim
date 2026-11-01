import { useEffect, useState } from "react";
import { Universe } from "./scene/Universe";
import { useStore } from "./store";
import { TopBar } from "./panels/TopBar";
import { Dock } from "./panels/Dock";
import { Inspector } from "./panels/Inspector";
import { Transport } from "./panels/Transport";
import { ReplayBar } from "./panels/ReplayBar";
import { Toasts } from "./panels/Toasts";
import { ProofExplorer } from "./panels/ProofExplorer";
import { Tour } from "./panels/Tour";

export function App() {
  const init = useStore(s => s.init);
  const error = useStore(s => s.error);
  const ready = useStore(s => s.ready);
  const [tourOpen, setTourOpen] = useState(false);

  useEffect(() => { void init(); }, [init]);

  useEffect(() => {
    const onKey = (e: KeyboardEvent) => {
      const tag = (e.target as HTMLElement).tagName;
      if (tag === "INPUT" || tag === "SELECT" || tag === "TEXTAREA") return;
      const s = useStore.getState();
      if (e.code === "Space") { e.preventDefault(); s.setPlaying(!s.playing); }
      if (e.key === "." && !s.playing) s.stepOnce();
      if (e.key === "Escape") { s.closeExplorer(); s.select(null); }
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, []);

  return (
    <div className="app">
      <div className="viewport"><Universe /></div>
      <TopBar onTour={() => setTourOpen(o => !o)} />
      <Dock />
      <Inspector />
      <Transport />
      <ReplayBar />
      <Toasts />
      <ProofExplorer />
      {tourOpen && <Tour onClose={() => setTourOpen(false)} />}
      {error && (
        <div className="fatal" role="alert">
          <strong>{ready ? "The backend reported a problem" : "No connection to the universe"}</strong>
          <span>{error}</span>
        </div>
      )}
    </div>
  );
}

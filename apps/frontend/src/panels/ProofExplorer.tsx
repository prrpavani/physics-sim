import { useEffect, useRef, useState } from "react";
import { useStore } from "../store";

const LAYERS = [
  { id: "evolution", label: "Does it stay true?" },
  { id: "rule", label: "Can it exist?" },
  { id: "transition", label: "Is it well defined?" },
] as const;

export function ProofExplorer() {
  const open = useStore(s => s.explorerOpen);
  const close = useStore(s => s.closeExplorer);
  const focus = useStore(s => s.proofFocus);
  const theorems = useStore(s => s.theorems);
  const [query, setQuery] = useState("");
  const focused = useRef<HTMLElement>(null);

  useEffect(() => {
    if (open && focus) focused.current?.scrollIntoView({ block: "center" });
    if (open) setQuery("");
  }, [open, focus]);
  if (!open) return null;

  const q = query.toLowerCase();
  const shown = theorems.filter(t => !q || t.statement.toLowerCase().includes(q) || t.id.toLowerCase().includes(q));

  return (
    <div className="explorer-backdrop" onClick={close}>
      <div className="explorer" role="dialog" aria-label="Proof explorer" onClick={e => e.stopPropagation()}>
        <header>
          <div>
            <h2>What Lean has proved</h2>
            <p className="lede">Each theorem is checked by Lean's kernel. Each one says exactly what it says, and no more.</p>
          </div>
          <button type="button" className="icon" aria-label="Close" onClick={close}>×</button>
        </header>
        <input className="search" placeholder="Search theorems" aria-label="Search theorems" value={query} onChange={e => setQuery(e.target.value)} />
        {LAYERS.map(layer => {
          const items = shown.filter(t => t.layer === layer.id);
          if (items.length === 0) return null;
          return (
            <section key={layer.id}>
              <h3>{layer.label}</h3>
              {items.map(t => (
                <article key={t.id} className={`theorem ${t.id === focus ? "focus" : ""}`} ref={t.id === focus ? focused : undefined}>
                  <p className="statement">{t.statement}</p>
                  <code>{t.id}</code>
                  {t.assumptions.length > 0 && (
                    <div className="assumption-block"><span>Assuming</span>
                      <ul>{t.assumptions.map((a, i) => <li key={i}>{a}</li>)}</ul>
                    </div>
                  )}
                  <p className="does-not-say"><span>Does not say</span> {t.doesNotSay}</p>
                </article>
              ))}
            </section>
          );
        })}
      </div>
    </div>
  );
}

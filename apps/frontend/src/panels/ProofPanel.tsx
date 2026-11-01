import { useState, type ReactNode } from "react";
import type { Card, Status } from "../api";
import { useStore } from "../store";

const LABEL: Record<Status, string> = { proven: "Proven", counterexample: "Counterexample", unproven: "Unproven" };

/** Lean source with a little colour. The text is exactly what the backend read from the proof files. */
function LeanCode({ text }: { text: string }) {
  const parts: ReactNode[] = [];
  const pattern = /(\/--[\s\S]*?-\/)|\b(theorem|by|have|exact|intro|obtain|induction|with|rw|refine|unfold|show|fun|split|simp|rfl)\b/g;
  let last = 0;
  for (const m of text.matchAll(pattern)) {
    parts.push(text.slice(last, m.index));
    parts.push(<span key={m.index} className={m[1] ? "lean-doc" : "lean-key"}>{m[0]}</span>);
    last = m.index + m[0].length;
  }
  parts.push(text.slice(last));
  return <pre className="lean"><code>{parts}</code></pre>;
}

function PromiseCard({ card, open, onToggle }: { card: Card; open: boolean; onToggle: () => void }) {
  const proofs = useStore(s => s.proofs);
  const startReplay = useStore(s => s.startReplay);
  const liveBroken = useStore(s => (card.key === "speedLimit" && s.broken.speedLimit) || (card.key === "staysInside" && s.broken.staysInside));
  return (
    <section className={`card ${card.status}`}>
      <button type="button" className="card-head" aria-expanded={open} onClick={onToggle}>
        <span className="lamp" />
        <span className="card-title">{card.title}</span>
        <span className="card-status">{LABEL[card.status]}</span>
      </button>
      <p className="meaning">{card.meaning}</p>
      {liveBroken && <p className="live-broken">Broken right now in this universe.</p>}
      {card.trace && (
        <button type="button" className="hot" onClick={() => startReplay(card)}>Replay how it breaks</button>
      )}
      {open && (
        <div className="card-body">
          <p className="status-text">{card.statusText}</p>
          {card.conditions.length > 0 && (
            <ul className="conditions">
              {card.conditions.map(c => (
                <li key={c.text} className={c.met ? "met" : "unmet"}><span aria-hidden>{c.met ? "✓" : "✗"}</span>{c.text}</li>
              ))}
            </ul>
          )}
          <p className="insight">{card.insight}</p>
          <h3>The Lean proof</h3>
          {card.theorems.map(t => <LeanCode key={t} text={proofs?.proofs[t] ?? "This proof's source file was not found."} />)}
          <p className="limits"><strong>What this does not say.</strong> {card.limits}</p>
        </div>
      )}
    </section>
  );
}

export function ProofPanel() {
  const cards = useStore(s => s.cards);
  const checking = useStore(s => s.checking);
  const proofs = useStore(s => s.proofs);
  const [open, setOpen] = useState<string | null>("speedLimit");
  const [showHow, setShowHow] = useState(false);
  return (
    <aside className="panel proofs" aria-label="What Lean proves">
      <header className="proofs-head">
        <h2>What Lean proves</h2>
        {checking && <span className="spinner" aria-label="Lean is checking" />}
      </header>
      {cards.map(c => <PromiseCard key={c.key} card={c} open={open === c.key} onToggle={() => setOpen(open === c.key ? null : c.key)} />)}
      <button type="button" className="link" aria-expanded={showHow} onClick={() => setShowHow(s => !s)}>
        {showHow ? "Hide" : "Why trust these answers?"}
      </button>
      {showHow && proofs && (
        <div className="how">
          <p>Every state on screen is computed by the Lean model in exact fractions. These theorems tie the answers above to the proofs. Each proof is checked by Lean's kernel, using only the axioms {proofs.axioms.join(", ")}.</p>
          {proofs.general.map(t => <LeanCode key={t} text={proofs.proofs[t] ?? ""} />)}
        </div>
      )}
    </aside>
  );
}

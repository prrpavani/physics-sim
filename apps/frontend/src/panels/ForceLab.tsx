import { useEffect, useMemo, useState } from "react";
import type { LawExpr } from "../../../../shared/types/paradox";
import { api, type FormulaCheck } from "../api";
import { frac, num } from "../lib/num";
import * as pretty from "../lib/pretty";
import { useStore } from "../store";
import { LawSlider, StatusPill } from "./common";
import { ExprEditor } from "./ExprEditor";

const c = (v: string): LawExpr => ({ type: "const", value: v });
const mul = (a: LawExpr, b: LawExpr): LawExpr => ({ type: "mul", a, b });
const add = (a: LawExpr, b: LawExpr): LawExpr => ({ type: "add", a, b });
const div = (a: LawExpr, b: LawExpr): LawExpr => ({ type: "div", a, b });
const masses = mul({ type: "massA" }, { type: "massB" });
const charges = mul({ type: "chargeA" }, { type: "chargeB" });
const rCubed = mul({ type: "distSquared" }, { type: "dist" });

const TEMPLATES: { name: string; about: string; formula: LawExpr }[] = [
  { name: "None", about: "Objects ignore each other.", formula: c("0") },
  { name: "Newton's gravity", about: "Attraction falling with distance squared.", formula: div(mul(c("20"), masses), add(c("1/10"), rCubed)) },
  { name: "Anti-gravity", about: "Everything repels everything.", formula: { type: "neg", a: div(mul(c("20"), masses), add(c("1/10"), rCubed)) } },
  { name: "Electric", about: "Like charges repel. Opposites attract.", formula: { type: "neg", a: div(mul(c("20"), charges), add(c("1/10"), rCubed)) } },
  { name: "Springs", about: "The further apart, the harder the pull.", formula: c("1/4") },
  { name: "Short range", about: "Strong up close, nothing far away.", formula: div(c("6"), add(c("1/10"), { type: "pow", a: { type: "dist" }, n: 4 })) },
  { name: "Speed-sensitive", about: "Fast objects pull harder.", formula: div(mul(c("1/4"), add(c("1"), { type: "speedSquared" })), add(c("1"), { type: "distSquared" })) },
  { name: "Undefined at contact", about: "Divides by r, so it has no value at r = 0.", formula: div(c("4"), { type: "dist" }) },
];

function Plot({ check }: { check: FormulaCheck | null }) {
  const path = useMemo(() => {
    if (!check) return null;
    const pts = check.samples.filter(s => s.force !== null && Number.isFinite(s.force));
    if (pts.length < 2) return null;
    const sorted = pts.map(p => Math.abs(p.force!)).sort((a, b) => a - b);
    const scale = Math.max(sorted[Math.floor(sorted.length * 0.92)], 1e-6);
    const W = 300, H = 110;
    const rMax = check.samples[check.samples.length - 1].r || 1;
    const X = (r: number) => (r / rMax) * W;
    const Y = (f: number) => H / 2 - Math.max(-1.1, Math.min(1.1, f / scale)) * (H / 2 - 6);
    return { d: pts.map((p, i) => `${i === 0 ? "M" : "L"}${X(p.r).toFixed(1)} ${Y(p.force!).toFixed(1)}`).join(" "), W, H, scale };
  }, [check]);
  return (
    <figure className="plot">
      <svg viewBox="0 0 300 110" role="img" aria-label="Force against distance">
        <line x1="0" y1="55" x2="300" y2="55" className="axis" />
        {path && <path d={path.d} className="curve" />}
        <text x="4" y="12" className="axis-label">pull</text>
        <text x="4" y="106" className="axis-label">push</text>
        <text x="270" y="50" className="axis-label">r → 20</text>
      </svg>
      <figcaption>Force between two objects of mass 2 and charge 1, computed by the Lean model.</figcaption>
    </figure>
  );
}

export function ForceLab() {
  const laws = useStore(s => s.world?.laws);
  const send = useStore(s => s.send);
  const audit = useStore(s => s.audit);
  const openExplorer = useStore(s => s.openExplorer);
  const [draft, setDraft] = useState<LawExpr>(laws?.pairForce ?? c("0"));
  const [check, setCheck] = useState<FormulaCheck | null>(null);
  const [problem, setProblem] = useState<string | null>(null);

  useEffect(() => {
    const abort = new AbortController();
    const t = setTimeout(() => {
      api.checkFormula(draft, abort.signal)
        .then(r => { setCheck(r); setProblem(null); })
        .catch(e => { if (!abort.signal.aborted) setProblem((e as Error).message); });
    }, 200);
    return () => { clearTimeout(t); abort.abort(); };
  }, [draft]);

  if (!laws) return null;
  const momentum = audit?.momentumBetweenBodies;
  return (
    <div className="tab">
      <h2>Force Lab</h2>
      <p className="lede">Invent the force between objects. Write any formula: Lean has proved that, with Newton's third law on, <em>every</em> formula keeps total momentum.</p>

      <div className="template-row">
        {TEMPLATES.map(t => (
          <button key={t.name} type="button" className="chip" title={t.about} onClick={() => setDraft(t.formula)}>{t.name}</button>
        ))}
      </div>

      <div className="formula-display">
        <span className="formula-prefix">F =</span>
        <code>{pretty.formula(draft)}</code>
        <span className="formula-suffix">× the line between them</span>
      </div>
      <ExprEditor value={draft} onChange={setDraft} />
      {problem && <p className="warn-text">{problem}</p>}
      <Plot check={check} />
      {check && (
        <div className="check-row">
          <StatusPill status={check.status} />
          <span>{check.explanation}</span>
        </div>
      )}
      <button type="button" className="primary wide" onClick={() => send({ type: "setPairForce", formula: draft })}>
        Make this the law of the universe
      </button>

      <h3>Newton's third law</h3>
      <LawSlider label="Reaction factor" value={num(laws.reaction)} min={-1} max={2} step={0.05}
        onCommit={v => send({ type: "setReaction", value: frac(v) })}
        hint="1: every pull is matched by an equal pull back. 0: nothing pulls back." />
      <div className="check-row">
        {momentum ? <StatusPill status={momentum.status} /> : <span className="muted">Checking…</span>}
        <span>
          {momentum?.status === "proven" && "Bodies acting on each other cannot change total momentum."}
          {momentum?.status === "counterexample" && "These objects really do change total momentum when they act on each other."}
          {momentum?.status === "unknown" && "The theorem's conditions do not hold, and these objects show no change right now."}
        </span>
      </div>
      {momentum?.theoremId && (
        <button type="button" className="link" onClick={() => openExplorer(momentum.theoremId)}>See the theorem</button>
      )}
    </div>
  );
}

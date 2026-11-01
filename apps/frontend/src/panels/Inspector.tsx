import { useState } from "react";
import type { Claim, Cmp, Constraint, Property, Status, Verdict } from "../../../../shared/types/paradox";
import * as pretty from "../lib/pretty";
import { useStore, verdictOf } from "../store";
import { NumberInput, Select, StatusPill } from "./common";

const PROPERTIES: Property[] = ["boundedPosition", "boundedVelocity", "positiveMass", "safeEnvironment", "uniqueIds"];
const CMP: { value: Cmp; label: string }[] = [
  { value: "lt", label: "<" }, { value: "le", label: "≤" }, { value: "eq", label: "=" }, { value: "ge", label: "≥" }, { value: "gt", label: ">" },
];
type Quantity = "population" | "mass" | "charge" | "speedSquared" | "velocityX" | "positionY" | "gravityY" | "maxSpeed" | "restitution";
const QUANTITIES: { value: Quantity; label: string }[] = [
  { value: "population", label: "Number of objects" },
  { value: "speedSquared", label: "Every object: speed²" },
  { value: "mass", label: "Every object: mass" },
  { value: "charge", label: "Every object: charge" },
  { value: "velocityX", label: "Every object: x velocity" },
  { value: "positionY", label: "Every object: height" },
  { value: "gravityY", label: "Law: gravity (up)" },
  { value: "maxSpeed", label: "Law: speed limit" },
  { value: "restitution", label: "Law: bounciness" },
];

function makeConstraint(q: Quantity, cmp: Cmp, value: string): Constraint {
  if (q === "population") return { type: "population", cmp, value };
  if (q === "gravityY" || q === "maxSpeed" || q === "restitution") return { type: "law", quantity: q, cmp, value };
  return { type: "body", quantity: q, cmp, value };
}

function Assumptions({ items }: { items: string[] }) {
  if (items.length === 0) return null;
  return <ul className="assume">{items.map((a, i) => <li key={i}>{a}</li>)}</ul>;
}

function VerdictActions({ v, claim }: { v?: Verdict; claim: Claim }) {
  const startReplay = useStore(s => s.startReplay);
  const find = useStore(s => s.findCounterexample);
  const searching = useStore(s => s.searching);
  const openExplorer = useStore(s => s.openExplorer);
  return (
    <div className="row tight">
      {v?.counterexample && (
        <button type="button" className="hot" onClick={() => {
          if (v.counterexample!.events.length === 0) void find(claim, v.scope ?? "allowed");
          else startReplay(v.counterexample!, claim, v.scope ?? "allowed");
        }}>Replay it</button>
      )}
      {!v?.counterexample && (
        <button type="button" disabled={searching} onClick={() => void find(claim, "any")}
          title="Look for a run that breaks this, using any event, including ones a protected universe would refuse.">
          {searching ? "Searching…" : "Try to break it"}
        </button>
      )}
      {v?.theoremId && <button type="button" className="link" onClick={() => openExplorer(v.theoremId)}>Theorem</button>}
    </div>
  );
}

function Guarantee({ p }: { p: Property }) {
  const live = useStore(s => s.guarantees?.[p]);
  const verdict = useStore(s => verdictOf(s.consistency, p));
  const [open, setOpen] = useState(false);
  const status: Status | "violated" = live === "violated" ? "violated" : live === "proven" ? "proven" : verdict?.status ?? "unknown";
  return (
    <li className={`guarantee ${status}`}>
      <button type="button" className="row-button" aria-expanded={open} onClick={() => setOpen(o => !o)}>
        <StatusPill status={status} compact />
        <span className="g-name">{pretty.propertyName[p]}</span>
        <span className="g-status">{status === "violated" ? "Broken now" : pretty.statusLabel[status as Status]}</span>
      </button>
      {open && (
        <div className="g-detail">
          <p>{pretty.propertyMeaning[p]}</p>
          {verdict && <p className="explain">{verdict.explanation}</p>}
          {verdict && <Assumptions items={verdict.assumptions} />}
          <VerdictActions v={verdict} claim={p} />
        </div>
      )}
    </li>
  );
}

function Layer({ tag, title, status, children, defaultOpen, busy }: {
  tag: string; title: string; status?: Status; children: React.ReactNode; defaultOpen?: boolean; busy?: boolean;
}) {
  const [open, setOpen] = useState(defaultOpen ?? false);
  return (
    <section className={`layer ${status ?? ""}`}>
      <button type="button" className="layer-head" aria-expanded={open} onClick={() => setOpen(o => !o)}>
        <span className="layer-tag">{tag}</span>
        <span className="layer-title">{title}</span>
        {busy ? <span className="spinner" aria-label="Lean is checking" /> : status ? <StatusPill status={status} /> : null}
      </button>
      {open && <div className="layer-body">{children}</div>}
    </section>
  );
}

function ConstraintBuilder() {
  const constraints = useStore(s => s.constraints);
  const setConstraints = useStore(s => s.setConstraints);
  const [q, setQ] = useState<Quantity>("population");
  const [cmp, setCmp] = useState<Cmp>("le");
  const [value, setValue] = useState("20");
  return (
    <div className="constraints">
      <ul className="constraint-list">
        {constraints.map((c, i) => (
          <li key={i}>
            <span>{pretty.constraint(c)}</span>
            <button type="button" className="icon" aria-label="Remove requirement" onClick={() => setConstraints(constraints.filter((_, j) => j !== i))}>×</button>
          </li>
        ))}
      </ul>
      <div className="constraint-form">
        <Select label="Quantity" value={q} options={QUANTITIES} onChange={setQ} />
        <Select label="Comparison" value={cmp} options={CMP} onChange={setCmp} />
        <NumberInput label="Value" value={value} onChange={setValue} />
        <button type="button" onClick={() => setConstraints([...constraints, makeConstraint(q, cmp, value)])}>Require</button>
      </div>
      <div className="row tight">
        <button type="button" className="chip" onClick={() => setConstraints([
          { type: "body", quantity: "speedSquared", cmp: "eq", value: "0" },
          { type: "body", quantity: "speedSquared", cmp: "eq", value: "25" },
        ])}>Try: stationary and moving</button>
        {constraints.length > 0 && <button type="button" className="link" onClick={() => setConstraints([])}>Clear</button>}
      </div>
    </div>
  );
}

function AuditRow({ name, status, text, verdict }: { name: string; status: Status; text?: string; verdict?: Verdict }) {
  const startReplay = useStore(s => s.startReplay);
  const openExplorer = useStore(s => s.openExplorer);
  return (
    <li className="audit-row">
      <StatusPill status={status} compact />
      <div>
        <strong>{name}</strong>
        <span>{text ?? verdict?.explanation}</span>
        {verdict?.assumptions && verdict.assumptions.length > 0 && <Assumptions items={verdict.assumptions} />}
        <div className="row tight">
          {verdict?.counterexample && (
            <button type="button" className="hot" onClick={() => startReplay(verdict.counterexample!, verdict.claim, verdict.scope ?? "timeOnly")}>Replay it</button>
          )}
          {verdict?.theoremId && verdict.status === "proven" && (
            <button type="button" className="link" onClick={() => openExplorer(verdict.theoremId)}>Theorem</button>
          )}
        </div>
      </div>
    </li>
  );
}

export function Inspector() {
  const consistency = useStore(s => s.consistency);
  const audit = useStore(s => s.audit);
  const checking = useStore(s => s.checking);
  const checkError = useStore(s => s.checkError);
  const searchNote = useStore(s => s.searchNote);
  const openExplorer = useStore(s => s.openExplorer);
  const [collapsed, setCollapsed] = useState(false);
  const rule = consistency?.ruleConsistency;
  const transition = consistency?.transitionConsistency;
  const evolution = consistency?.evolutionConsistency.verdicts ?? [];
  const constraintVerdicts = evolution.filter(v => typeof v.claim !== "string" && v.claim.type === "constraint");
  const evolutionStatus: Status | undefined = evolution.length === 0 ? undefined
    : evolution.some(v => v.status === "counterexample") ? "counterexample"
    : evolution.some(v => v.status === "unknown") ? "unknown" : "proven";

  if (collapsed) {
    return <button type="button" className="inspector-open" onClick={() => setCollapsed(false)}>Consistency</button>;
  }

  return (
    <aside className="inspector" aria-label="Consistency inspector">
      <header className="inspector-head">
        <h2>Consistency</h2>
        <button type="button" className="link" onClick={() => openExplorer()}>All theorems</button>
        <button type="button" className="icon" aria-label="Hide" onClick={() => setCollapsed(true)}>×</button>
      </header>
      {checkError && <p className="warn-text">{checkError}</p>}
      {searchNote && <p className="note">{searchNote}</p>}

      <Layer tag="C" title="Does it stay true?" status={evolutionStatus} defaultOpen busy={checking}>
        <ul className="guarantees">{PROPERTIES.map(p => <Guarantee key={p} p={p} />)}</ul>
        {constraintVerdicts.map((v, i) => (
          <div key={i} className="constraint-verdict">
            <StatusPill status={v.status} />
            <span>{pretty.claim(v.claim)}</span>
            <p className="explain">{v.explanation}</p>
            <VerdictActions v={v} claim={v.claim} />
          </div>
        ))}
      </Layer>

      <Layer tag="A" title="Can it exist?" status={rule?.status} busy={checking}>
        <p className="explain">{rule?.explanation}</p>
        {rule?.conflict && (
          <div className="conflict">
            {rule.conflict.map((c, i) => <span key={i}>{pretty.constraint(c)}</span>)}
          </div>
        )}
        {rule?.witness && <p className="note">Lean checked a real example: {rule.witness.bodies.length} object{rule.witness.bodies.length === 1 ? "" : "s"} meeting every requirement.</p>}
        <ConstraintBuilder />
        {rule && <Assumptions items={rule.assumptions} />}
      </Layer>

      <Layer tag="B" title="Is it well defined?" status={transition?.status} busy={checking}>
        <p className="explain">{transition?.explanation}</p>
        {transition && transition.portalsWithoutExit.length > 0 && <p className="issue">{transition.portalsWithoutExit.length} portal{transition.portalsWithoutExit.length === 1 ? "" : "s"} with no destination</p>}
        {transition?.missingRegions.map(r => <p key={r} className="issue">A rule names “{r}”, which does not exist</p>)}
        {transition?.undefinedFormulas.map(f => <p key={f} className="issue">The {f} formula divides by zero for some inputs</p>)}
        {transition?.unknownFormulas.map(f => <p key={f} className="issue quiet">The {f} formula could not be proved defined</p>)}
        {transition && transition.ruleConflicts.length > 0 && <p className="issue">{transition.ruleConflicts.length} pair{transition.ruleConflicts.length === 1 ? "" : "s"} of rules give different results depending on order. The rule list decides.</p>}
      </Layer>

      <Layer tag="∑" title="What is conserved?" busy={checking}>
        {audit && (
          <ul className="audit">
            <AuditRow name="Momentum between objects" status={audit.momentumBetweenBodies.status} text={audit.momentumBetweenBodies.assumptions.join(" ")} />
            <AuditRow name="Momentum over a full step" status={audit.momentumFullStep.every(v => v.status === "unknown") ? "unknown" : "counterexample"} verdict={audit.momentumFullStep.find(v => v.counterexample)} />
            <AuditRow name="Energy never rises" status={audit.energy.status} verdict={audit.energy} />
            <AuditRow name="Total mass" status={audit.mass.status} verdict={audit.mass} />
            <AuditRow name="Number of objects" status={audit.population.status} verdict={audit.population} />
          </ul>
        )}
      </Layer>
    </aside>
  );
}

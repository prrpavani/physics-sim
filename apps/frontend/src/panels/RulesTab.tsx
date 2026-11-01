import { useEffect, useState } from "react";
import type { BodyAction, BodyCond, Rule, RuleReport, WorldAction, WorldCond } from "../../../../shared/types/paradox";
import { api } from "../api";
import { vec } from "../lib/num";
import * as pretty from "../lib/pretty";
import { useStore } from "../store";
import { NumberInput, Select, StatusPill } from "./common";

/** One action card, either on bodies or on the laws. */
type ActionKind =
  | "scaleVelocity" | "reverseVelocity" | "rotateVelocity" | "clampVelocity" | "applyForce" | "teleport" | "clampPosition"
  | "scaleMass" | "massFromSpeed" | "setCharge" | "destroy" | "create"
  | "setGravity" | "reverseGravity" | "setMaxSpeed" | "setMassRate";

interface ActionCard { kind: ActionKind; value: string }
type WhenKind = "always" | "gravityAbove" | "gravityChanged" | "everyTicks";
type WhichKind = "all" | "speedAbove" | "onColor" | "inRegion";

interface Graph {
  when: WhenKind; whenValue: string;
  which: WhichKind; whichValue: string;
  actions: ActionCard[];
}

const WHEN: { value: WhenKind; label: string; placeholder?: string }[] = [
  { value: "always", label: "Every step" },
  { value: "everyTicks", label: "Every N steps", placeholder: "50" },
  { value: "gravityChanged", label: "Gravity changes" },
  { value: "gravityAbove", label: "Gravity is above", placeholder: "10" },
];
const WHICH: { value: WhichKind; label: string }[] = [
  { value: "all", label: "Every object" },
  { value: "speedAbove", label: "Objects faster than" },
  { value: "onColor", label: "Objects on colour" },
  { value: "inRegion", label: "Objects in region" },
];
const ACTIONS: { value: ActionKind; label: string; takes?: string }[] = [
  { value: "scaleVelocity", label: "Multiply velocity by", takes: "2" },
  { value: "reverseVelocity", label: "Reverse velocity" },
  { value: "rotateVelocity", label: "Turn velocity" },
  { value: "clampVelocity", label: "Enforce the speed limit" },
  { value: "applyForce", label: "Push upward with force", takes: "5" },
  { value: "teleport", label: "Teleport upward by", takes: "1" },
  { value: "clampPosition", label: "Bring back inside" },
  { value: "scaleMass", label: "Multiply mass by", takes: "2" },
  { value: "massFromSpeed", label: "Heavier when faster, by", takes: "0.01" },
  { value: "setCharge", label: "Set charge to", takes: "1" },
  { value: "destroy", label: "Destroy the object" },
  { value: "create", label: "Create a new object" },
  { value: "setGravity", label: "Set gravity (up) to", takes: "-10" },
  { value: "reverseGravity", label: "Reverse gravity" },
  { value: "setMaxSpeed", label: "Set the speed limit to", takes: "20" },
  { value: "setMassRate", label: "Set mass rate to", takes: "1" },
];

const bodyActionOf = (a: ActionCard): BodyAction | null => {
  switch (a.kind) {
    case "scaleVelocity": return { type: "scaleVelocity", factor: a.value };
    case "reverseVelocity": return { type: "reverseVelocity" };
    case "rotateVelocity": return { type: "rotateVelocity" };
    case "clampVelocity": return { type: "clampVelocity" };
    case "applyForce": return { type: "applyForce", force: { x: "0", y: a.value, z: "0" } };
    case "teleport": return { type: "translate", by: { x: "0", y: a.value, z: "0" } };
    case "clampPosition": return { type: "clampPosition" };
    case "scaleMass": return { type: "scaleMass", factor: a.value };
    case "massFromSpeed":
      return { type: "setMassFormula", formula: { type: "add", a: { type: "massA" }, b: { type: "mul", a: { type: "const", value: a.value }, b: { type: "speedSquared" } } } };
    case "setCharge": return { type: "setCharge", charge: a.value };
    default: return null;
  }
};

const worldActionOf = (a: ActionCard): WorldAction | null => {
  switch (a.kind) {
    case "setGravity": return { type: "setGravity", gravity: { x: "0", y: a.value, z: "0" } };
    case "reverseGravity": return { type: "reverseGravity" };
    case "setMaxSpeed": return { type: "setMaxSpeed", value: a.value };
    case "setMassRate": return { type: "setMassRate", value: a.value };
    default: return null;
  }
};

function compile(g: Graph): Rule {
  const which: BodyCond =
    g.which === "speedAbove" ? { type: "speedAbove", speed: g.whichValue || "0" }
    : g.which === "onColor" ? { type: "onColor", color: g.whichValue }
    : g.which === "inRegion" ? { type: "inRegion", name: g.whichValue }
    : { type: "all" };
  const steps: Rule[] = g.actions.map(a => {
    if (a.kind === "destroy") return { type: "destroy", condition: which };
    if (a.kind === "create") {
      return { type: "create", template: {
        id: 0, shape: { type: "sphere", radius: "1/2" }, position: vec(0, 0, 0), velocity: vec(1, 2, 0), mass: "1", charge: "0",
      } };
    }
    const body = bodyActionOf(a);
    if (body) return { type: "body", condition: which, action: body };
    return { type: "world", action: worldActionOf(a)! };
  });
  let rule: Rule = steps.length === 0 ? { type: "skip" } : steps.reduceRight((rest, s) => ({ type: "seq", first: s, then: rest }));
  if (g.when !== "always") {
    const c: WorldCond =
      g.when === "everyTicks" ? { type: "everyTicks", n: Number(g.whenValue) || 50 }
      : g.when === "gravityAbove" ? { type: "gravityAbove", value: g.whenValue || "0" }
      : { type: "gravityChanged" };
    rule = { type: "when", condition: c, rule };
  }
  return rule;
}

const RECIPES: { name: string; about: string; graph: Graph }[] = [
  { name: "Velocity ×100", about: "Multiplies every velocity. It will break the speed limit.",
    graph: { when: "always", whenValue: "", which: "all", whichValue: "", actions: [{ kind: "scaleVelocity", value: "100" }] } },
  { name: "×100, then limited", about: "The same multiplier, followed by the speed limiter. Lean proves it safe.",
    graph: { when: "always", whenValue: "", which: "all", whichValue: "", actions: [{ kind: "scaleVelocity", value: "100" }, { kind: "clampVelocity", value: "" }] } },
  { name: "Heavier when faster", about: "Mass grows with speed. Lean proves mass stays positive.",
    graph: { when: "always", whenValue: "", which: "all", whichValue: "", actions: [{ kind: "massFromSpeed", value: "0.01" }] } },
  { name: "Flip gravity every 50", about: "Gravity reverses on a schedule.",
    graph: { when: "everyTicks", whenValue: "50", which: "all", whichValue: "", actions: [{ kind: "reverseGravity", value: "" }] } },
  { name: "Reverse on red", about: "Reverses anything on a red region.",
    graph: { when: "always", whenValue: "", which: "onColor", whichValue: "red", actions: [{ kind: "reverseVelocity", value: "" }] } },
  { name: "Destroy the fast", about: "Removes anything over a speed.",
    graph: { when: "always", whenValue: "", which: "speedAbove", whichValue: "15", actions: [{ kind: "destroy", value: "" }] } },
  { name: "Life every 100", about: "Creates an object on a schedule, if it is valid.",
    graph: { when: "everyTicks", whenValue: "100", which: "all", whichValue: "", actions: [{ kind: "create", value: "" }] } },
  { name: "Teleporter", about: "Moves everything up each step. It can leave the world.",
    graph: { when: "always", whenValue: "", which: "all", whichValue: "", actions: [{ kind: "teleport", value: "1" }] } },
];

export function RulesTab() {
  const world = useStore(s => s.world);
  const send = useStore(s => s.send);
  const mode = useStore(s => s.mode);
  const [graph, setGraph] = useState<Graph>(RECIPES[0].graph);
  const [report, setReport] = useState<RuleReport | null>(null);
  const [problem, setProblem] = useState<string | null>(null);

  const rule = compile(graph);
  const ruleKey = JSON.stringify(rule);
  useEffect(() => {
    if (!world) return;
    const t = setTimeout(() => {
      api.validateRule(rule, world)
        .then(r => { setReport(r.rules[0]); setProblem(null); })
        .catch(e => setProblem((e as Error).message));
    }, 200);
    return () => clearTimeout(t);
  }, [ruleKey, world?.regions.length]);

  if (!world) return null;
  const whenInfo = WHEN.find(w => w.value === graph.when)!;
  const needsWhich = graph.which !== "all";

  const updateAction = (i: number, a: ActionCard) => {
    const actions = [...graph.actions]; actions[i] = a; setGraph({ ...graph, actions });
  };

  return (
    <div className="tab">
      <h2>Rules</h2>
      <p className="lede">Rules run at the end of every step. Lean's rule checker reads each one and says what it can guarantee, for every universe it could run in.</p>

      <div className="template-row">
        {RECIPES.map(r => (
          <button key={r.name} type="button" className="chip" title={r.about} onClick={() => setGraph(r.graph)}>{r.name}</button>
        ))}
      </div>

      <div className="rule-graph">
        <div className="node when">
          <span className="node-tag">When</span>
          <Select label="When" value={graph.when} options={WHEN} onChange={when => setGraph({ ...graph, when, whenValue: WHEN.find(w => w.value === when)?.placeholder ?? "" })} />
          {whenInfo.placeholder && <NumberInput label="Value" value={graph.whenValue} step={1} onChange={whenValue => setGraph({ ...graph, whenValue })} />}
        </div>
        <div className="wire" aria-hidden />
        <div className="node which">
          <span className="node-tag">Which</span>
          <Select label="Which objects" value={graph.which} options={WHICH} onChange={which => setGraph({ ...graph, which, whichValue: "" })} />
          {needsWhich && (
            <input className="num-input text" aria-label="Value" value={graph.whichValue} placeholder={graph.which === "speedAbove" ? "15" : graph.which === "onColor" ? "red" : "name"}
              onChange={e => setGraph({ ...graph, whichValue: e.target.value })} />
          )}
        </div>
        {graph.actions.map((a, i) => {
          const info = ACTIONS.find(x => x.value === a.kind)!;
          return (
            <div key={i} className="node-wrap">
              <div className="wire" aria-hidden />
              <div className="node then">
                <span className="node-tag">{i === 0 ? "Do" : "Then"}</span>
                <Select label="Action" value={a.kind} options={ACTIONS}
                  onChange={kind => updateAction(i, { kind, value: ACTIONS.find(x => x.value === kind)?.takes ?? "" })} />
                {info.takes && <NumberInput label="Value" value={a.value} onChange={value => updateAction(i, { ...a, value })} />}
                {graph.actions.length > 1 && (
                  <button type="button" className="icon" aria-label="Remove this step" onClick={() => setGraph({ ...graph, actions: graph.actions.filter((_, j) => j !== i) })}>×</button>
                )}
              </div>
            </div>
          );
        })}
        <button type="button" className="add-node" onClick={() => setGraph({ ...graph, actions: [...graph.actions, { kind: "clampVelocity", value: "" }] })}>+ Add a step</button>
      </div>

      <p className="rule-sentence">{pretty.rule(rule)}</p>
      {problem && <p className="warn-text">{problem}</p>}

      {report && (
        <div className="rule-report">
          <div className="check-row">
            <StatusPill status={report.status} />
            <span>{report.explanation}</span>
          </div>
          <div className="keep-grid">
            {report.keeps.map(k => (
              <span key={k.property} className={`keep ${k.cleared ? "yes" : "no"}`}>
                {k.cleared ? "✓" : "?"} {pretty.propertyName[k.property]}
              </span>
            ))}
          </div>
          {!report.certified && report.repair && (
            <p className="note">Protected mode would add limiters after this rule, which Lean can prove safe.</p>
          )}
          {!report.certified && !report.repair && (
            <p className="note">Protected mode would reject this rule. No repair is available.</p>
          )}
        </div>
      )}

      <button type="button" className="primary wide" onClick={() => send({ type: "addRule", rule })}>
        Add to the universe {mode === "unprotected" ? "(unprotected)" : ""}
      </button>

      <h3>Rules in this universe</h3>
      {world.rules.length === 0 && <p className="muted">None yet.</p>}
      <ol className="rule-list">
        {world.rules.map((r, i) => (
          <li key={i}>
            <span>{pretty.rule(r)}</span>
            <button type="button" className="icon" aria-label="Remove rule"
              onClick={() => send([{ type: "clearRules" }, ...world.rules.filter((_, j) => j !== i).map(x => ({ type: "addRule" as const, rule: x }))])}>×</button>
          </li>
        ))}
      </ol>
    </div>
  );
}

// A visual builder for force formulas. It only edits data. The backend evaluates it.

import type { LawExpr } from "../../../../shared/types/paradox";

const LEAVES: { type: LawExpr["type"]; label: string }[] = [
  { type: "const", label: "number" },
  { type: "massA", label: "m₁" }, { type: "massB", label: "m₂" },
  { type: "chargeA", label: "q₁" }, { type: "chargeB", label: "q₂" },
  { type: "dist", label: "r" }, { type: "distSquared", label: "r²" }, { type: "speedSquared", label: "v²" },
];
const OPS: { type: LawExpr["type"]; label: string }[] = [
  { type: "add", label: "a + b" }, { type: "sub", label: "a − b" }, { type: "mul", label: "a × b" },
  { type: "div", label: "a ÷ b" }, { type: "neg", label: "− a" }, { type: "pow", label: "a ^ n" },
];

function change(e: LawExpr, type: LawExpr["type"]): LawExpr {
  const first: LawExpr = "a" in e ? e.a : e;
  const second: LawExpr = "b" in e ? e.b : { type: "const", value: "1" };
  switch (type) {
    case "const": return { type, value: "1" };
    case "add": case "sub": case "mul": case "div": return { type, a: first, b: second };
    case "neg": return { type, a: first };
    case "pow": return { type, a: first, n: 2 };
    default: return { type } as LawExpr;
  }
}

export function ExprEditor({ value, onChange, depth = 0 }: { value: LawExpr; onChange: (e: LawExpr) => void; depth?: number }) {
  return (
    <div className={`expr depth-${Math.min(depth, 3)}`}>
      <select className="expr-kind" aria-label="Formula piece" value={value.type} onChange={e => onChange(change(value, e.target.value as LawExpr["type"]))}>
        <optgroup label="Values">{LEAVES.map(o => <option key={o.type} value={o.type}>{o.label}</option>)}</optgroup>
        <optgroup label="Operations">{OPS.map(o => <option key={o.type} value={o.type}>{o.label}</option>)}</optgroup>
      </select>
      {value.type === "const" && (
        <input className="num-input" aria-label="Number" value={value.value} onChange={e => onChange({ type: "const", value: e.target.value })} />
      )}
      {"a" in value && (
        <div className="expr-kids">
          <ExprEditor value={value.a} depth={depth + 1} onChange={a => onChange({ ...value, a })} />
          {"b" in value && <ExprEditor value={value.b} depth={depth + 1} onChange={b => onChange({ ...value, b })} />}
          {value.type === "pow" && (
            <label className="pow-n">power
              <input className="num-input" type="number" min={0} max={16} value={value.n}
                onChange={e => onChange({ ...value, n: Math.max(0, Math.min(16, Number(e.target.value) || 0)) })} />
            </label>
          )}
        </div>
      )}
    </div>
  );
}

// Small shared controls.

import { useEffect, useRef, useState } from "react";
import type { Status } from "../../../../shared/types/paradox";
import { statusLabel } from "../lib/pretty";

export function StatusPill({ status, compact }: { status: Status | "violated"; compact?: boolean }) {
  const label = status === "violated" ? "Broken" : statusLabel[status];
  return (
    <span className={`status ${status}`} title={label}>
      <span className="lamp" />{compact ? null : label}
    </span>
  );
}

/** A slider that shows its value right away and sends after the user pauses. */
export function LawSlider(props: {
  label: string; hint?: string; value: number; min: number; max: number; step: number; unit?: string;
  onCommit: (v: number) => void; danger?: (v: number) => string | null;
}) {
  const { label, hint, value, min, max, step, unit, onCommit, danger } = props;
  const [local, setLocal] = useState(value);
  const active = useRef(false);
  const timer = useRef<ReturnType<typeof setTimeout>>(undefined);

  useEffect(() => { if (!active.current) setLocal(value); }, [value]);

  const digits = step >= 1 ? 0 : step >= 0.1 ? 1 : step >= 0.01 ? 2 : 3;
  const warning = danger?.(local) ?? null;

  return (
    <div className={`slider ${warning ? "warned" : ""}`}>
      <div className="slider-head">
        <label>{label}</label>
        <output>{local.toFixed(digits)}{unit ?? ""}</output>
      </div>
      <input type="range" aria-label={label} min={min} max={max} step={step} value={local}
        onChange={e => {
          const v = Number(e.target.value);
          setLocal(v);
          active.current = true;
          clearTimeout(timer.current);
          timer.current = setTimeout(() => { active.current = false; onCommit(v); }, 160);
        }} />
      {warning ? <small className="warn-text">{warning}</small> : hint ? <small>{hint}</small> : null}
    </div>
  );
}

export function Select<T extends string>(props: {
  value: T; onChange: (v: T) => void; options: { value: T; label: string }[]; label?: string;
}) {
  return (
    <select className="select" aria-label={props.label} value={props.value} onChange={e => props.onChange(e.target.value as T)}>
      {props.options.map(o => <option key={o.value} value={o.value}>{o.label}</option>)}
    </select>
  );
}

export function NumberInput({ value, onChange, label, step = 0.5 }: {
  value: string; onChange: (v: string) => void; label?: string; step?: number;
}) {
  return (
    <input className="num-input" type="number" aria-label={label} step={step} value={value}
      onChange={e => onChange(e.target.value)} />
  );
}

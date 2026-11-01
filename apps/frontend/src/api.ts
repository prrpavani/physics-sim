// The only path to the universe. Every state on screen comes from these calls.

import type {
  Claim, Constraint, ConsistencyResponse, Decision, EnvironmentEvent, EventScope, Frame, LawExpr, Property,
  RuleReport, Rule, Status, TheoremInfo, Trace, Verdict, World,
} from "../../../shared/types/paradox";

async function post<T>(path: string, body: unknown, signal?: AbortSignal): Promise<T> {
  const res = await fetch(`/api/universe/${path}`, {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify(body),
    signal,
  });
  const data = await res.json();
  if (!res.ok) throw new Error(data.error ?? `The backend answered ${res.status}`);
  return data as T;
}

async function get<T>(path: string): Promise<T> {
  const res = await fetch(`/api/${path}`);
  if (!res.ok) throw new Error(`The backend answered ${res.status}`);
  return (await res.json()) as T;
}

export type GuaranteeStatus = "proven" | "unknown" | "violated";
export type Guarantees = Record<Property, GuaranteeStatus>;
export interface LiveFrame extends Omit<Frame, "violations"> {
  event: EnvironmentEvent;
  guarantees: Guarantees;
}
export interface RunResult {
  frames: LiveFrame[];
  world: World;
  guarantees: Guarantees;
  nextChaosSeed: number | null;
}
export interface Preset { name: string; title: string; description: string }
export interface AuditItem {
  status: Status;
  theoremId: string | null;
  basis: string;
  assumptions: string[];
}
export interface Audit {
  mass: Verdict;
  energy: Verdict;
  population: Verdict;
  momentumBetweenBodies: AuditItem;
  momentumFullStep: Verdict[];
}
export interface FormulaCheck {
  status: Status;
  explanation: string;
  theoremId: string | null;
  samples: { r: number; force: number | null }[];
  momentumConserved: string;
  momentumTheorem: string;
}
export interface Chaos { seed: number; rate: number; kind: "safe" | "wild" }

export const api = {
  health: () => get<{ status: string; contractVersion: string }>("health"),
  theorems: () => get<{ theorems: TheoremInfo[] }>("theorems"),
  presets: () => get<{ presets: Preset[] }>("presets"),
  create: (preset: string, seed: number) =>
    post<{ world: World; preset: string; seed: number; guaranteed: boolean }>("create", { preset, seed }),
  run: (req: {
    world: World; steps: number; events?: EnvironmentEvent[]; mode: "protected" | "unprotected";
    constraints?: Constraint[]; chaos?: Chaos;
  }) => post<RunResult>("run", req),
  consistency: (world: World, constraints: Constraint[], signal?: AbortSignal) =>
    post<ConsistencyResponse>("check-consistency", { world, constraints }, signal),
  audit: (world: World, signal?: AbortSignal) => post<Audit>("audit-laws", { world }, signal),
  validateRule: (rule: Rule, world: World) =>
    post<{ rules: RuleReport[] }>("validate-rules", { rule, world }),
  counterexample: (world: World, claim: Claim, scope: EventScope) =>
    post<{ status: Status; counterexample: Trace | null; checked: boolean; explanation?: string }>(
      "find-counterexample", { world, claim, scope }),
  checkTrace: (trace: Trace, claim: Claim, scope: EventScope) =>
    post<{ valid: boolean; replays: boolean; inScope: boolean; breaksClaim: boolean }>(
      "check-trace", { trace, claim, scope }),
  checkEvent: (world: World, event: EnvironmentEvent) =>
    post<{ allowed: boolean; decision: Decision }>("check-event", { world, event }),
  checkFormula: (formula: LawExpr, signal?: AbortSignal) =>
    post<FormulaCheck>("check-formula", { formula, massA: "2", massB: "2", chargeA: "1", chargeB: "1" }, signal),
};

// The only path to the universe. Every state on screen comes from these calls.

export interface Vec3 { x: string; y: string; z: string }
export interface Body {
  id: number; position: Vec3; velocity: Vec3; mass: string; radius: string;
  /** For drawing only. Floating-point approximations, never formal values. Ignored by the backend. */
  draw?: [number, number, number];
  drawVelocity?: [number, number, number];
}
export interface Bounds { minX: string; maxX: string; minY: string; maxY: string; minZ: string; maxZ: string }
export interface Laws {
  gravity: string; pull: string; thirdLaw: boolean; restitution: string; multiplier: string; limiter: boolean;
  maxSpeed: string; timeStep: string; grid: number;
}
export interface World { bodies: Body[]; bounds: Bounds; laws: Laws; tick: number }
export interface Broken { staysInside: boolean; speedLimit: boolean }
export interface Frame { tick: number; bodies: Body[]; broken: Broken }
export type Decision = "accepted" | "repaired" | "refused";
export interface RunResult { frames: Frame[]; world: World; laws: Laws; decision: Decision | null }
export interface Trace { start: World; states: World[] }
export type Status = "proven" | "counterexample" | "unproven";
export interface Card {
  key: string; title: string; meaning: string; insight: string; limits: string;
  status: Status; statusText: string;
  conditions: { text: string; met: boolean }[];
  theorems: string[];
  trace: Trace | null;
  fromProbe: boolean;
}
export interface Proofs { proofs: Record<string, string | null>; general: string[]; axioms: string[] }

async function call<T>(method: string, path: string, body?: unknown, signal?: AbortSignal): Promise<T> {
  const res = await fetch(`/api/${path}`, {
    method,
    headers: { "content-type": "application/json" },
    body: body === undefined ? undefined : JSON.stringify(body),
    signal,
  });
  const data = await res.json();
  if (!res.ok) throw new Error(data.error ?? `The backend answered ${res.status}`);
  return data as T;
}

export const api = {
  create: () => call<{ world: World }>("POST", "create"),
  run: (req: { world: World; steps: number; locked: boolean; laws: Laws | null }) => call<RunResult>("POST", "run", req),
  verdicts: (world: World, signal?: AbortSignal) => call<{ cards: Card[] }>("POST", "verdicts", { world }, signal),
  proofs: () => call<Proofs>("GET", "proofs"),
};

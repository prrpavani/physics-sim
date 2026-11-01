// Talks to the Lean server at /api. If the server is not there, falls back to the mock engine
// and reports that, so the UI can show it.

import * as mock from "./mock-engine.js";

let useMock = null;

async function serverUp() {
  if (useMock !== null) return !useMock;
  try {
    const r = await fetch("/api/world?seed=1", { cache: "no-store" });
    useMock = !(r.ok && (r.headers.get("content-type") || "").includes("json"));
  } catch {
    useMock = true;
  }
  return !useMock;
}

export async function newWorld(seed) {
  if (!(await serverUp())) return mock.generateWorld(seed);
  const r = await fetch(`/api/world?seed=${seed}`);
  return (await r.json()).world;
}

export async function step(request) {
  if (!(await serverUp())) return mock.step(request);
  const r = await fetch("/api/step", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(request),
  });
  if (!r.ok) throw new Error(`The Lean server answered ${r.status}`);
  return r.json();
}

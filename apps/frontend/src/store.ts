// All app state. The simulation clock lives outside React so the scene can read it each frame
// without re-rendering panels. Worlds and frames only ever come from the backend.

import { create } from "zustand";
import type {
  Claim, Constraint, ConsistencyResponse, EnvironmentEvent, EventScope, Property, TheoremInfo, Trace, Verdict, World,
} from "../../../shared/types/paradox";
import { api, type Audit, type Guarantees, type LiveFrame, type Preset } from "./api";
import * as pretty from "./lib/pretty";

export type Mode = "protected" | "unprotected";

export interface LogEntry {
  id: number;
  tick: number;
  text: string;
  kind: "accepted" | "repaired" | "rejected" | "info" | "broke";
  detail?: string;
}

export interface Toast { id: number; kind: LogEntry["kind"]; title: string; detail?: string }

export interface Replay {
  trace: Trace;
  claim: Claim;
  scope: EventScope;
  index: number;
  playing: boolean;
  checked?: { valid: boolean; replays: boolean; breaksClaim: boolean };
}

/** The clock. Frames wait here until the scene shows them. */
export const clock = {
  queue: [] as LiveFrame[],
  current: null as LiveFrame | null,
  previous: null as LiveFrame | null,
  /** How far between previous and current the scene is, from 0 to 1. */
  alpha: 1,
  /** The world after the last frame received. The next request starts from here. */
  latest: null as World | null,
  fetching: false,
  generation: 0,
};

const BATCH = 16;
const LOW_WATER = 8;

interface State {
  ready: boolean;
  error: string | null;
  presets: Preset[];
  theorems: TheoremInfo[];
  presetName: string;
  seed: number;

  world: World | null;
  initial: World | null;
  mode: Mode;
  playing: boolean;
  speed: number;
  pending: EnvironmentEvent[];
  constraints: Constraint[];
  chaosRate: number;
  chaosKind: "safe" | "wild";
  chaosSeed: number;

  tick: number;
  guarantees: Guarantees | null;
  selected: number | null;
  showVectors: boolean;
  showTrails: boolean;

  log: LogEntry[];
  toasts: Toast[];

  consistency: ConsistencyResponse | null;
  audit: Audit | null;
  checking: boolean;
  checkError: string | null;
  revision: number;

  replay: Replay | null;
  searching: boolean;
  searchNote: string | null;
  proofFocus: string | null;
  explorerOpen: boolean;

  init: () => Promise<void>;
  open: (preset: string, seed?: number) => Promise<void>;
  reset: () => Promise<void>;
  setMode: (m: Mode) => void;
  setPlaying: (p: boolean) => void;
  setSpeed: (s: number) => void;
  send: (e: EnvironmentEvent | EnvironmentEvent[]) => void;
  stepOnce: () => void;
  pump: () => void;
  onFrame: (f: LiveFrame) => void;
  setConstraints: (c: Constraint[]) => void;
  setChaos: (rate: number, kind?: "safe" | "wild") => void;
  setChaosSeed: (s: number) => void;
  select: (id: number | null) => void;
  toggleVectors: () => void;
  toggleTrails: () => void;
  dismissToast: (id: number) => void;
  recheck: () => void;
  findCounterexample: (claim: Claim, scope: EventScope) => Promise<void>;
  startReplay: (trace: Trace, claim: Claim, scope: EventScope) => void;
  setReplayIndex: (i: number) => void;
  toggleReplayPlaying: () => void;
  exitReplay: () => void;
  openExplorer: (focus?: string | null) => void;
  closeExplorer: () => void;
}

let nextId = 1;
let checkTimer: ReturnType<typeof setTimeout> | undefined;
let checkAbort: AbortController | undefined;

export const useStore = create<State>((set, get) => {
  const addLog = (entry: Omit<LogEntry, "id">) => {
    const id = nextId++;
    set(s => ({ log: [{ ...entry, id }, ...s.log].slice(0, 200) }));
  };
  const toast = (kind: Toast["kind"], title: string, detail?: string) => {
    const id = nextId++;
    set(s => ({ toasts: [...s.toasts, { id, kind, title, detail }].slice(-3) }));
    setTimeout(() => get().dismissToast(id), kind === "accepted" ? 2600 : 6000);
  };

  /** Ask the backend for the next frames, including any events the user has sent. */
  const fetchFrames = async (steps: number) => {
    const s = get();
    if (clock.fetching || !clock.latest) return;
    clock.fetching = true;
    const generation = clock.generation;
    const events = s.pending;
    set({ pending: [] });
    try {
      const result = await api.run({
        world: clock.latest,
        steps: Math.max(steps, events.length),
        events,
        mode: s.mode,
        constraints: s.mode === "protected" ? s.constraints : [],
        chaos: s.chaosRate > 0 ? { seed: s.chaosSeed, rate: s.chaosRate, kind: s.chaosKind } : undefined,
      });
      if (generation !== clock.generation) return;
      clock.latest = result.world;
      clock.queue.push(...result.frames);
      const changed = events.length > 0;
      set({
        world: result.world,
        chaosSeed: result.nextChaosSeed ?? get().chaosSeed,
        error: null,
        revision: changed ? get().revision + 1 : get().revision,
      });
      if (changed) get().recheck();
    } catch (err) {
      set({ error: (err as Error).message, playing: false, pending: [...events, ...get().pending] });
    } finally {
      clock.fetching = false;
    }
  };

  return {
    ready: false, error: null, presets: [], theorems: [], presetName: "normal", seed: 42,
    world: null, initial: null, mode: "protected", playing: true, speed: 1, pending: [],
    constraints: [], chaosRate: 0, chaosKind: "safe", chaosSeed: 7,
    tick: 0, guarantees: null, selected: null, showVectors: false, showTrails: true,
    log: [], toasts: [],
    consistency: null, audit: null, checking: false, checkError: null, revision: 0,
    replay: null, searching: false, searchNote: null, proofFocus: null, explorerOpen: false,

    init: async () => {
      try {
        const [{ presets }, { theorems }] = await Promise.all([api.presets(), api.theorems()]);
        set({ presets, theorems, ready: true });
        await get().open("normal", 42);
      } catch (err) {
        set({ error: `Cannot reach the Lean backend. Start it with “make run”. (${(err as Error).message})` });
      }
    },

    open: async (preset, seed) => {
      const useSeed = seed ?? get().seed;
      try {
        const { world } = await api.create(preset, useSeed);
        clock.generation += 1;
        clock.queue = [];
        clock.latest = world;
        clock.fetching = false;
        const first: LiveFrame = {
          tick: world.tick, bodies: world.bodies, decision: null,
          event: { type: "idle" }, guarantees: get().guarantees ?? ({} as Guarantees),
        };
        clock.current = first;
        clock.previous = first;
        clock.alpha = 1;
        set({
          world, initial: world, presetName: preset, seed: useSeed, pending: [], tick: world.tick, selected: null,
          replay: null, error: null, revision: get().revision + 1, searchNote: null,
        });
        addLog({ tick: 0, kind: "info", text: `Opened “${get().presets.find(p => p.name === preset)?.title ?? preset}”, seed ${useSeed}` });
        get().recheck();
      } catch (err) {
        set({ error: (err as Error).message });
      }
    },

    reset: async () => {
      const { initial } = get();
      if (!initial) return;
      clock.generation += 1;
      clock.queue = [];
      clock.latest = initial;
      clock.fetching = false;
      const first: LiveFrame = {
        tick: initial.tick, bodies: initial.bodies, decision: null,
        event: { type: "idle" }, guarantees: get().guarantees ?? ({} as Guarantees),
      };
      clock.current = first;
      clock.previous = first;
      clock.alpha = 1;
      set({ world: initial, pending: [], tick: initial.tick, replay: null, revision: get().revision + 1 });
      addLog({ tick: 0, kind: "info", text: "Universe reset" });
      get().recheck();
    },

    setMode: mode => {
      set({ mode });
      addLog({ tick: get().tick, kind: "info", text: mode === "protected" ? "Protected mode on" : "Unprotected mode on" });
    },
    setPlaying: playing => set({ playing }),
    setSpeed: speed => set({ speed }),

    send: e => {
      const events = Array.isArray(e) ? e : [e];
      set(s => ({ pending: [...s.pending, ...events] }));
      if (!get().playing) void fetchFrames(events.length);
    },

    stepOnce: () => {
      if (get().replay) return;
      if (clock.queue.length === 0) void fetchFrames(1);
      else get().onFrame(clock.queue.shift()!);
    },

    pump: () => {
      const s = get();
      if (s.replay || !s.playing || !clock.latest) return;
      if (clock.queue.length < LOW_WATER) void fetchFrames(BATCH);
    },

    onFrame: frame => {
      const before = clock.current;
      clock.previous = before ?? frame;
      clock.current = frame;
      clock.alpha = 0;
      const previous = get().guarantees;
      set({ tick: frame.tick, guarantees: frame.guarantees });

      const d = frame.decision;
      if (d?.result === "rejected") {
        addLog({ tick: frame.tick, kind: "rejected", text: pretty.event(d.event), detail: "Rejected: this would not keep every guarantee." });
        toast("rejected", "Rejected by protected mode", pretty.event(d.event));
      } else if (d?.result === "repaired") {
        addLog({ tick: frame.tick, kind: "repaired", text: pretty.event(d.event), detail: `Asked for: ${pretty.event(d.original)}` });
        toast("repaired", "Repaired to stay safe", `${pretty.event(d.original)} → ${pretty.event(d.event)}`);
      } else if (frame.event.type !== "idle") {
        addLog({ tick: frame.tick, kind: "accepted", text: pretty.event(frame.event) });
      }

      if (previous) {
        for (const key of Object.keys(frame.guarantees) as Property[]) {
          if (frame.guarantees[key] === "violated" && previous[key] !== "violated") {
            addLog({ tick: frame.tick, kind: "broke", text: `${pretty.propertyName[key]} broke`, detail: pretty.propertyMeaning[key] });
            toast("broke", `${pretty.propertyName[key]} broke`, `At step ${frame.tick}. Lean computed this state.`);
          }
        }
      }
    },

    setConstraints: constraints => {
      set(s => ({ constraints, revision: s.revision + 1 }));
      get().recheck();
    },
    setChaos: (chaosRate, kind) => set(s => ({ chaosRate, chaosKind: kind ?? s.chaosKind })),
    setChaosSeed: chaosSeed => set({ chaosSeed }),
    select: selected => set({ selected }),
    toggleVectors: () => set(s => ({ showVectors: !s.showVectors })),
    toggleTrails: () => set(s => ({ showTrails: !s.showTrails })),
    dismissToast: id => set(s => ({ toasts: s.toasts.filter(t => t.id !== id) })),

    recheck: () => {
      clearTimeout(checkTimer);
      checkTimer = setTimeout(async () => {
        const world = clock.latest;
        if (!world) return;
        checkAbort?.abort();
        const abort = new AbortController();
        checkAbort = abort;
        set({ checking: true, checkError: null });
        try {
          const constraints = get().constraints;
          const [consistency, audit] = await Promise.all([
            api.consistency(world, constraints, abort.signal),
            api.audit(world, abort.signal),
          ]);
          if (!abort.signal.aborted) set({ consistency, audit, checking: false });
        } catch (err) {
          if (!abort.signal.aborted) set({ checking: false, checkError: (err as Error).message });
        }
      }, 450);
    },

    findCounterexample: async (claim, scope) => {
      const latest = clock.latest;
      const { initial } = get();
      if (!latest) return;
      set({ searching: true, searchNote: null });
      try {
        let result = await api.counterexample(latest, claim, scope);
        // If the world is already broken, the shortest run has no steps and shows nothing. Search
        // again from the original objects, under the current laws and rules, to show how it breaks.
        if (result.counterexample?.events.length === 0 && initial) {
          const fresh: World = { ...latest, bodies: initial.bodies, tick: 0, nextId: initial.nextId };
          const again = await api.counterexample(fresh, claim, scope);
          if (again.counterexample && again.counterexample.events.length > 0) result = again;
        }
        if (result.counterexample) get().startReplay(result.counterexample, claim, scope);
        else set({ searchNote: result.explanation ?? "No counterexample was found within the limits." });
      } catch (err) {
        set({ searchNote: (err as Error).message });
      } finally {
        set({ searching: false });
      }
    },

    startReplay: (trace, claim, scope) => {
      set({ replay: { trace, claim, scope, index: 0, playing: true }, playing: false, explorerOpen: false });
      addLog({ tick: get().tick, kind: "broke", text: `Replaying a counterexample: ${pretty.claim(claim)}` });
      void api.checkTrace(trace, claim, scope).then(checked => {
        set(s => (s.replay?.trace === trace ? { replay: { ...s.replay, checked } } : {}));
      });
    },
    setReplayIndex: index => set(s => (s.replay ? { replay: { ...s.replay, index, playing: false } } : {})),
    toggleReplayPlaying: () => set(s => (s.replay ? { replay: { ...s.replay, playing: !s.replay.playing } } : {})),
    exitReplay: () => set({ replay: null, playing: true }),
    openExplorer: (focus = null) => set({ explorerOpen: true, proofFocus: focus }),
    closeExplorer: () => set({ explorerOpen: false }),
  };
});

/** All verdicts from the last consistency check, for looking up by claim. */
export function verdictOf(c: ConsistencyResponse | null, property: Property): Verdict | undefined {
  return c?.evolutionConsistency.verdicts.find(v =>
    typeof v.claim !== "string" && v.claim.type === "property" && v.claim.property === property);
}

export const TICKS_PER_SECOND = 50;

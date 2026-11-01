// App state. The clock lives outside React so the scene can read it every frame without re-rendering
// the panels. Worlds and frames only ever come from the backend.

import { create } from "zustand";
import { api, type Broken, type Card, type Frame, type Laws, type Proofs, type Trace, type World } from "./api";

/** Frames waiting to be shown. */
export const clock = {
  queue: [] as Frame[],
  current: null as Frame | null,
  previous: null as Frame | null,
  alpha: 1,
  /** The world after the last frame received. The next request starts from here. */
  latest: null as World | null,
  fetching: false,
  generation: 0,
};

const BATCH = 16;
const LOW_WATER = 8;
export const TICKS_PER_SECOND = 50;

export interface Replay { trace: Trace; title: string; fromProbe: boolean; index: number; playing: boolean }

interface State {
  error: string | null;
  world: World | null;
  laws: Laws | null;
  locked: boolean;
  playing: boolean;
  tick: number;
  broken: Broken;
  notice: string | null;
  cards: Card[];
  checking: boolean;
  proofs: Proofs | null;
  replay: Replay | null;
  pendingLaws: Laws | null;

  init: () => Promise<void>;
  reset: () => Promise<void>;
  setLaws: (change: Partial<Laws>) => void;
  setLocked: (on: boolean) => void;
  setPlaying: (on: boolean) => void;
  stepOnce: () => void;
  pump: () => void;
  onFrame: (f: Frame) => void;
  check: () => void;
  startReplay: (card: Card) => void;
  setReplayIndex: (i: number) => void;
  toggleReplay: () => void;
  exitReplay: () => void;
}

let checkTimer: ReturnType<typeof setTimeout> | undefined;
let checkAbort: AbortController | undefined;
let noticeTimer: ReturnType<typeof setTimeout> | undefined;

const showFrame = (world: World): Frame => ({
  tick: world.tick, bodies: world.bodies, broken: { staysInside: false, speedLimit: false },
});

export const useStore = create<State>((set, get) => {
  const notify = (notice: string) => {
    clearTimeout(noticeTimer);
    set({ notice });
    noticeTimer = setTimeout(() => set({ notice: null }), 7000);
  };

  const fetchFrames = async (steps: number) => {
    const s = get();
    if (clock.fetching || !clock.latest) return;
    clock.fetching = true;
    const generation = clock.generation;
    const requested = s.pendingLaws;
    set({ pendingLaws: null });
    try {
      const result = await api.run({ world: clock.latest, steps, locked: s.locked, laws: requested });
      if (generation !== clock.generation) return;
      clock.latest = result.world;
      clock.queue.push(...result.frames);
      set({ world: result.world, error: null });
      if (requested) {
        if (!get().pendingLaws) set({ laws: result.laws });
        if (result.decision === "repaired") {
          notify("Keep it consistent turned the limiter on, because these laws could break the speed limit. Switch it off to watch them break.");
        }
        if (result.decision === "refused") notify("Those laws are not meaningful, so nothing changed.");
        get().check();
      }
    } catch (err) {
      set({ error: (err as Error).message, playing: false });
    } finally {
      clock.fetching = false;
    }
  };

  const restart = (world: World) => {
    clock.generation += 1;
    clock.queue = [];
    clock.latest = world;
    clock.fetching = false;
    clock.current = showFrame(world);
    clock.previous = clock.current;
    clock.alpha = 1;
    set({ world, laws: world.laws, tick: world.tick, pendingLaws: null, replay: null, playing: true, notice: null,
      broken: { staysInside: false, speedLimit: false } });
    get().check();
  };

  return {
    error: null, world: null, laws: null, locked: true, playing: true, tick: 0,
    broken: { staysInside: false, speedLimit: false }, notice: null, cards: [], checking: false,
    proofs: null, replay: null, pendingLaws: null,

    init: async () => {
      try {
        const [{ world }, proofs] = await Promise.all([api.create(), api.proofs()]);
        set({ proofs });
        restart(world);
      } catch (err) {
        set({ error: `Cannot reach the Lean backend. Start it with “make run”. (${(err as Error).message})` });
      }
    },

    reset: async () => {
      const { world } = await api.create();
      restart(world);
    },

    setLaws: change => {
      const laws = get().laws;
      if (!laws) return;
      const next = { ...laws, ...change };
      set({ laws: next, pendingLaws: next });
      if (!get().playing) void fetchFrames(1);
    },

    setLocked: locked => {
      set({ locked });
      // Turning the lock on applies it to the laws already in force.
      if (locked && get().laws) get().setLaws({});
    },

    setPlaying: playing => set({ playing }),

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
      clock.previous = clock.current ?? frame;
      clock.current = frame;
      clock.alpha = 0;
      set({ tick: frame.tick, broken: frame.broken });
    },

    check: () => {
      clearTimeout(checkTimer);
      checkTimer = setTimeout(async () => {
        const world = clock.latest;
        if (!world) return;
        checkAbort?.abort();
        const abort = new AbortController();
        checkAbort = abort;
        set({ checking: true });
        try {
          const { cards } = await api.verdicts(world, abort.signal);
          if (!abort.signal.aborted) set({ cards, checking: false });
        } catch (err) {
          if (!abort.signal.aborted) set({ checking: false, error: (err as Error).message });
        }
      }, 250);
    },

    startReplay: card => {
      if (card.trace) {
        set({ replay: { trace: card.trace, title: card.title, fromProbe: card.fromProbe, index: 0, playing: true }, playing: false });
      }
    },
    setReplayIndex: index => set(s => (s.replay ? { replay: { ...s.replay, index, playing: false } } : {})),
    toggleReplay: () => set(s => (s.replay ? { replay: { ...s.replay, playing: !s.replay.playing } } : {})),
    exitReplay: () => set({ replay: null, playing: true }),
  };
});

import { useState } from "react";
import type { LawExpr, Rule } from "../../../../shared/types/paradox";
import { clock, useStore } from "../store";

const newton: LawExpr = {
  type: "div",
  a: { type: "mul", a: { type: "const", value: "20" }, b: { type: "mul", a: { type: "massA" }, b: { type: "massB" } } },
  b: { type: "add", a: { type: "const", value: "1/10" }, b: { type: "mul", a: { type: "distSquared" }, b: { type: "dist" } } },
};
const times100: Rule = { type: "body", action: { type: "scaleVelocity", factor: "100" } };

const STEPS: { title: string; text: string; action: string; run: () => Promise<void> | void }[] = [
  {
    title: "A universe with a promise",
    text: "Objects in a box, in protected mode. On the right: “Stays inside the world” is Proven. That is a theorem about every permitted future, not a test.",
    action: "Open it",
    run: async () => {
      const s = useStore.getState();
      s.setMode("protected"); s.setConstraints([]); s.setChaos(0, "safe");
      await s.open("normal", 42);
      useStore.getState().setPlaying(true);
    },
  },
  {
    title: "Unleash chaos",
    text: "Random changes to gravity, limits, force laws and space, from a reproducible seed. Lean has proved safe chaos keeps every guarantee, for every seed. So nothing here can break them.",
    action: "Start chaos",
    run: () => useStore.getState().setChaos(120, "safe"),
  },
  {
    title: "Invent a law of physics",
    text: "Replace the force between objects with attraction. Any formula is allowed. With Newton's third law on, Lean proved every formula anyone can write keeps total momentum.",
    action: "Switch on attraction",
    run: () => {
      const s = useStore.getState();
      s.setChaos(0, "safe");
      s.send([{ type: "disableGravity" }, { type: "setPairForce", formula: newton }, { type: "setReaction", value: "1" }]);
    },
  },
  {
    title: "Break Newton's third law",
    text: "Now nothing pulls back. Open “What is conserved?” on the right: momentum between objects stops being Proven, and Lean measures the change.",
    action: "Turn it off",
    run: () => useStore.getState().send({ type: "setReaction", value: "0" }),
  },
  {
    title: "Try to break the speed limit",
    text: "Add a rule that multiplies every velocity by 100. Protected mode will not allow it as written. It repairs the rule by adding limiters, which Lean can prove safe.",
    action: "Add the ×100 rule",
    run: () => useStore.getState().send({ type: "addRule", rule: times100 }),
  },
  {
    title: "Take the protection off",
    text: "In unprotected mode, the same rule goes through. Watch the walls: the speed limit breaks. Lean computed this state exactly.",
    action: "Go unprotected",
    run: async () => {
      const s = useStore.getState();
      await s.open("normal", 42);
      useStore.getState().setMode("unprotected");
      useStore.getState().send({ type: "addRule", rule: times100 });
      useStore.getState().setPlaying(true);
    },
  },
  {
    title: "Watch the proof of failure",
    text: "PARADOX finds the shortest run that breaks the limit and replays it. Lean checks that run against the real transition function, so it is evidence, not a claim.",
    action: "Replay the counterexample",
    run: async () => {
      await useStore.getState().findCounterexample("boundedVelocity", "allowed");
      void clock;
    },
  },
  {
    title: "Ask for the impossible",
    text: "Require every object to be stationary and also moving at speed 5. Open “Can it exist?”: Lean proves no universe with an object can do both.",
    action: "Require both",
    run: () => {
      const s = useStore.getState();
      s.exitReplay();
      s.setConstraints([
        { type: "body", quantity: "speedSquared", cmp: "eq", value: "0" },
        { type: "body", quantity: "speedSquared", cmp: "eq", value: "25" },
      ]);
    },
  },
];

export function Tour({ onClose }: { onClose: () => void }) {
  const [i, setI] = useState(0);
  const [busy, setBusy] = useState(false);
  const step = STEPS[i];
  return (
    <div className="tour" role="dialog" aria-label="Guided demo">
      <div className="tour-progress">{STEPS.map((_, j) => <span key={j} className={j <= i ? "on" : ""} />)}</div>
      <h3>{step.title}</h3>
      <p>{step.text}</p>
      <div className="row">
        <button type="button" className="primary" disabled={busy} onClick={async () => {
          setBusy(true);
          try { await step.run(); } finally { setBusy(false); }
          if (i < STEPS.length - 1) setI(i + 1);
        }}>{step.action}</button>
        <button type="button" className="ghost" onClick={() => (i > 0 ? setI(i - 1) : onClose())}>{i > 0 ? "Back" : "Close"}</button>
        <button type="button" className="link" onClick={onClose}>End</button>
      </div>
    </div>
  );
}

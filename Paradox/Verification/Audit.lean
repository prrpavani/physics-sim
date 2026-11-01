import Lean
import Paradox.Api.Tests

/-!
# Build-time audit

The build fails if a main theorem starts using `sorry` or a new axiom, or if a theorem's statement
starts depending on different definitions.

Kept apart from the rest of the library so the `paradox` executable does not link `Lean`.
-/

open Lean Elab Command

namespace Paradox.Audit

/-- The definitions a theorem's statement mentions, followed through their bodies. The proof is
not followed. -/
partial def specSurface (env : Environment) (thm : Name) : NameSet :=
  let rec go (todo : List Name) (seen : NameSet) : NameSet :=
    match todo with
    | [] => seen
    | c :: rest =>
      if seen.contains c then go rest seen else
      let next := match env.find? c with
        | some (.defnInfo d) => d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList
        | some ci => ci.type.getUsedConstants.toList
        | none => []
      go (next ++ rest) (seen.insert c)
  match env.find? thm with
  | some ci => go ci.type.getUsedConstants.toList {}
  | none => {}

/-- `#spec_surface thm` lists the PARADOX definitions a reader must trust to understand `thm`.
Generated names such as field accessors are left out. -/
elab "#spec_surface " id:ident : command => do
  let env ← getEnv
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let own := (specSurface env thm).toArray.filter fun c =>
    (`Paradox).isPrefixOf c && !c.isInternal && !Meta.isMatcherCore env c &&
      (env.getProjectionFnInfo? c).isNone && !env.isConstructor c &&
      !isRecCore env c && !isCasesOnRecursor env c &&
      !["ctorIdx", "below", "brecOn", "go", "decEq"].contains c.getString! &&
      !(c.getString!.startsWith "inst")
  logInfo m!"{(own.qsort Name.lt).toList}"

end Paradox.Audit

open Paradox

/-! ## Axioms -/

/-- info: 'Paradox.stays_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stays_inside

/-- info: 'Paradox.speedLimit_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms speedLimit_holds

/-- info: 'Paradox.momentum_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms momentum_holds

/-- info: 'Paradox.energy_never_rises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms energy_never_rises

/-- info: 'Paradox.verdict_proven_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms verdict_proven_sound

/-- info: 'Paradox.verdict_counterexample_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms verdict_counterexample_sound

/-- info: 'Paradox.checkTrace_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkTrace_sound

/-- info: 'Paradox.locked_run_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms locked_run_safe

/-! ## Trusted surface -/

/--
info: [Paradox.Body,
 Paradox.BodyOk,
 Paradox.Bounds,
 Paradox.EnergySafe,
 Paradox.FairStart,
 Paradox.Laws,
 Paradox.LawsOk,
 Paradox.MomentumKept,
 Paradox.MomentumSafe,
 Paradox.Promise,
 Paradox.SpeedSafe,
 Paradox.Status,
 Paradox.StaysInside,
 Paradox.Trace,
 Paradox.Vec3,
 Paradox.WellFormed,
 Paradox.WithinSpeedLimit,
 Paradox.World,
 Paradox.applyGravity,
 Paradox.checkTrace,
 Paradox.clamp,
 Paradox.clampAbs,
 Paradox.findCounterexample,
 Paradox.finishBody,
 Paradox.firstBreak,
 Paradox.forcesStage,
 Paradox.limitSpeed,
 Paradox.moveAxis,
 Paradox.moveBody,
 Paradox.pairAll,
 Paradox.pairOne,
 Paradox.probeWorld,
 Paradox.pullAmount,
 Paradox.pullPair,
 Paradox.pullStage,
 Paradox.run,
 Paradox.searchSteps,
 Paradox.snap,
 Paradox.tick,
 Paradox.totalEnergy,
 Paradox.totalMomentum,
 Paradox.trajectory,
 Paradox.tryStart,
 Paradox.verdict,
 Paradox.Bounds.Contains,
 Paradox.Bounds.Valid,
 Paradox.Bounds.clampPoint,
 Paradox.Bounds.inset,
 Paradox.Promise.Holds,
 Paradox.Promise.Safe,
 Paradox.Trace.final,
 Paradox.Vec3.WithinAbs,
 Paradox.Vec3.add,
 Paradox.Vec3.clampAbs,
 Paradox.Vec3.dot,
 Paradox.Vec3.scale,
 Paradox.Vec3.snap,
 Paradox.Vec3.sub]
-/
#guard_msgs in #spec_surface verdict_proven_sound

/--
info: [Paradox.Body,
 Paradox.BodyOk,
 Paradox.Bounds,
 Paradox.Decision,
 Paradox.Laws,
 Paradox.LawsOk,
 Paradox.SpeedSafe,
 Paradox.Vec3,
 Paradox.WellFormed,
 Paradox.WithinSpeedLimit,
 Paradox.World,
 Paradox.applyGravity,
 Paradox.clamp,
 Paradox.clampAbs,
 Paradox.decideLaws,
 Paradox.finishBody,
 Paradox.forcesStage,
 Paradox.limitSpeed,
 Paradox.lockedRun,
 Paradox.lockedSetLaws,
 Paradox.lockedStep,
 Paradox.moveAxis,
 Paradox.moveBody,
 Paradox.pairAll,
 Paradox.pairOne,
 Paradox.pullAmount,
 Paradox.pullPair,
 Paradox.pullStage,
 Paradox.snap,
 Paradox.tick,
 Paradox.Bounds.Valid,
 Paradox.Bounds.clampPoint,
 Paradox.Bounds.inset,
 Paradox.Vec3.WithinAbs,
 Paradox.Vec3.add,
 Paradox.Vec3.clampAbs,
 Paradox.Vec3.dot,
 Paradox.Vec3.scale,
 Paradox.Vec3.snap,
 Paradox.Vec3.sub]
-/
#guard_msgs in #spec_surface locked_run_safe

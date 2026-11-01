import Lean
import Paradox.Api.Catalog
import Paradox.Verification.Examples
import Paradox.Domains.Ecosystem

/-!
# Build-time audit

The build fails if a main theorem starts using `sorry` or a new axiom, or if a theorem's statement
starts depending on a different set of definitions.

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

/-- info: 'Paradox.run_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_inv

/-- info: 'Paradox.guaranteed_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms guaranteed_run

/-- info: 'Paradox.next_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms next_inv

/-- info: 'Paradox.protectedRun_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms protectedRun_safe

/-- info: 'Paradox.protectedRun_guaranteed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms protectedRun_guaranteed

/-- info: 'Paradox.enforcedRun_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms enforcedRun_holds

/-- info: 'Paradox.enforcedRun_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms enforcedRun_inv

/-- info: 'Paradox.random_chaos_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms random_chaos_safe

/-- info: 'Paradox.generateWorld_guaranteed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms generateWorld_guaranteed

/-- info: 'Paradox.Rule.keeps_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rule.keeps_sound

/-- info: 'Paradox.Rule.repair_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rule.repair_certified

/-- info: 'Paradox.checkTrace_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkTrace_sound

/-- info: 'Paradox.searchCounterexample_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms searchCounterexample_sound

/-- info: 'Paradox.verifyProperty_proven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms verifyProperty_proven

/-- info: 'Paradox.verifyProperty_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms verifyProperty_counterexample

/-- info: 'Paradox.proven_excludes_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms proven_excludes_counterexample

/-- info: 'Paradox.pairForces_conserve_momentum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pairForces_conserve_momentum

/-- info: 'Paradox.interaction_conserves_momentum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms interaction_conserves_momentum

/-- info: 'Paradox.bouncePair_energy_elastic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bouncePair_energy_elastic

/-- info: 'Paradox.tick_energy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tick_energy_le

/-- info: 'Paradox.idleRun_energy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms idleRun_energy_le

/-- info: 'Paradox.idleRun_conserves_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms idleRun_conserves_mass

/-- info: 'Paradox.merges_conserve_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms merges_conserve_mass

/-- info: 'Paradox.moveBody_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms moveBody_free

/-- info: 'Paradox.wrap_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wrap_mem

/-- info: 'Paradox.checkConstraints_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkConstraints_satisfiable

/-- info: 'Paradox.checkConstraints_contradiction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkConstraints_contradiction

/-- info: 'Paradox.LawExpr.divisionsSafe_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LawExpr.divisionsSafe_sound

/-- info: 'Paradox.orderStatus_conflict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms orderStatus_conflict

/-- info: 'Paradox.orderStatus_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms orderStatus_independent

/-- info: 'Paradox.negative_maxSpeed_violates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms negative_maxSpeed_violates

/-- info: 'Paradox.Domains.meadow_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Domains.meadow_run

/-! ## Trusted surface -/

/--
info: [Paradox.Allowed,
 Paradox.Body,
 Paradox.BodyAction,
 Paradox.BodyAllowed,
 Paradox.BodyCond,
 Paradox.BoundedPosition,
 Paradox.BoundedVelocity,
 Paradox.Bounds,
 Paradox.CanCreate,
 Paradox.CollisionMode,
 Paradox.EnvironmentEvent,
 Paradox.Field,
 Paradox.FitsIn,
 Paradox.Guaranteed,
 Paradox.Inv,
 Paradox.LawExpr,
 Paradox.LawInputs,
 Paradox.Metric,
 Paradox.PhysicsLaws,
 Paradox.Portal,
 Paradox.PortalEffect,
 Paradox.PositiveMass,
 Paradox.Property,
 Paradox.Region,
 Paradox.Rule,
 Paradox.SafeEnvironment,
 Paradox.Shape,
 Paradox.Topology,
 Paradox.Touching,
 Paradox.UniqueIds,
 Paradox.Vec3,
 Paradox.World,
 Paradox.WorldAction,
 Paradox.WorldCond,
 Paradox.accelerate,
 Paradox.applyEvent,
 Paradox.applyForces,
 Paradox.approxSqrt,
 Paradox.bouncePair,
 Paradox.childOf,
 Paradox.clamp,
 Paradox.clampAbs,
 Paradox.collisionStage,
 Paradox.evalRules,
 Paradox.exchangeMassPair,
 Paradox.exchangeVelocityPair,
 Paradox.externalAcceleration,
 Paradox.firstTouchingPair,
 Paradox.forcePair,
 Paradox.limitSpeed,
 Paradox.mergeAll,
 Paradox.mergeBodies,
 Paradox.mergeOne,
 Paradox.metricSquared,
 Paradox.moveAxis,
 Paradox.moveBody,
 Paradox.pairAll,
 Paradox.pairInputs,
 Paradox.pairOne,
 Paradox.portalAt,
 Paradox.ruleInputs,
 Paradox.run,
 Paradox.selfInputs,
 Paradox.snap,
 Paradox.spawnStage,
 Paradox.step,
 Paradox.throughPortals,
 Paradox.tick,
 Paradox.timeScaleAt,
 Paradox.updateBody,
 Paradox.withLaws,
 Paradox.wrap,
 Paradox.Body.extent,
 Paradox.BodyAction.apply,
 Paradox.BodyAction.keeps,
 Paradox.BodyCond.test,
 Paradox.Bounds.Contains,
 Paradox.Bounds.Valid,
 Paradox.Bounds.clampPoint,
 Paradox.Bounds.inset,
 Paradox.Engine.AllowedTrace,
 Paradox.LawExpr.eval,
 Paradox.LawExpr.sign,
 Paradox.PortalEffect.Safe,
 Paradox.PortalEffect.apply,
 Paradox.Property.all,
 Paradox.Property.holds,
 Paradox.Rule.certified,
 Paradox.Rule.envSafe,
 Paradox.Rule.establishes,
 Paradox.Rule.eval,
 Paradox.Rule.keeps,
 Paradox.Shape.extent,
 Paradox.Vec3.WithinAbs,
 Paradox.Vec3.add,
 Paradox.Vec3.clampAbs,
 Paradox.Vec3.cross,
 Paradox.Vec3.dot,
 Paradox.Vec3.neg,
 Paradox.Vec3.scale,
 Paradox.Vec3.snap,
 Paradox.Vec3.sub,
 Paradox.Vec3.zero,
 Paradox.WorldAction.apply,
 Paradox.WorldAction.keeps,
 Paradox.WorldCond.test]
-/
#guard_msgs in #spec_surface guaranteed_run

/--
info: [Paradox.Allowed,
 Paradox.Body,
 Paradox.BodyAction,
 Paradox.BodyAllowed,
 Paradox.BodyCond,
 Paradox.BodyQuantity,
 Paradox.BoundedPosition,
 Paradox.BoundedVelocity,
 Paradox.Bounds,
 Paradox.CanCreate,
 Paradox.Claim,
 Paradox.Cmp,
 Paradox.CollisionMode,
 Paradox.Constraint,
 Paradox.EnvironmentEvent,
 Paradox.EventScope,
 Paradox.Field,
 Paradox.FitsIn,
 Paradox.InScope,
 Paradox.Inv,
 Paradox.LawExpr,
 Paradox.LawInputs,
 Paradox.LawQuantity,
 Paradox.Metric,
 Paradox.PhysicsLaws,
 Paradox.Portal,
 Paradox.PortalEffect,
 Paradox.PositiveMass,
 Paradox.Property,
 Paradox.Region,
 Paradox.Rule,
 Paradox.SafeEnvironment,
 Paradox.SearchLimits,
 Paradox.Shape,
 Paradox.Status,
 Paradox.Topology,
 Paradox.Touching,
 Paradox.UniqueIds,
 Paradox.Vec3,
 Paradox.Verdict,
 Paradox.World,
 Paradox.WorldAction,
 Paradox.WorldCond,
 Paradox.WorldTrace,
 Paradox.accelerate,
 Paradox.applyEvent,
 Paradox.applyForces,
 Paradox.approxSqrt,
 Paradox.bigVectors,
 Paradox.bouncePair,
 Paradox.candidateEvents,
 Paradox.checkTrace,
 Paradox.childOf,
 Paradox.clamp,
 Paradox.clampAbs,
 Paradox.collisionStage,
 Paradox.evalRules,
 Paradox.exchangeMassPair,
 Paradox.exchangeVelocityPair,
 Paradox.externalAcceleration,
 Paradox.firstTouchingPair,
 Paradox.forcePair,
 Paradox.gentleCandidates,
 Paradox.kineticEnergy,
 Paradox.limitSpeed,
 Paradox.mergeAll,
 Paradox.mergeBodies,
 Paradox.mergeOne,
 Paradox.metricSquared,
 Paradox.momentumAlong,
 Paradox.moveAxis,
 Paradox.moveBody,
 Paradox.pairAll,
 Paradox.pairInputs,
 Paradox.pairOne,
 Paradox.portalAt,
 Paradox.probeBody,
 Paradox.provenAssumptions,
 Paradox.ruleInputs,
 Paradox.run,
 Paradox.searchCounterexample,
 Paradox.searchDepth,
 Paradox.searchLayer,
 Paradox.selfInputs,
 Paradox.snap,
 Paradox.spawnStage,
 Paradox.step,
 Paradox.throughPortals,
 Paradox.tick,
 Paradox.timeScaleAt,
 Paradox.total,
 Paradox.totalEnergy,
 Paradox.totalMass,
 Paradox.totalMomentum,
 Paradox.traceOf,
 Paradox.updateBody,
 Paradox.verifyProperty,
 Paradox.wildCandidates,
 Paradox.withLaws,
 Paradox.wrap,
 Paradox.Body.extent,
 Paradox.BodyAction.apply,
 Paradox.BodyAction.ctorElim,
 Paradox.BodyAction.ctorElimType,
 Paradox.BodyAction.keeps,
 Paradox.BodyCond.ctorElim,
 Paradox.BodyCond.ctorElimType,
 Paradox.BodyCond.noConfusion,
 Paradox.BodyCond.noConfusionType,
 Paradox.BodyCond.test,
 Paradox.BodyQuantity.value,
 Paradox.Bounds.Contains,
 Paradox.Bounds.Valid,
 Paradox.Bounds.clampPoint,
 Paradox.Bounds.inset,
 Paradox.Claim.holds,
 Paradox.Cmp.holds,
 Paradox.Constraint.holds,
 Paradox.Engine.AllowedTrace,
 Paradox.Engine.Trace,
 Paradox.Engine.statesOf,
 Paradox.EnvironmentEvent.ctorElim,
 Paradox.EnvironmentEvent.ctorElimType,
 Paradox.LawExpr.ctorElim,
 Paradox.LawExpr.ctorElimType,
 Paradox.LawExpr.eval,
 Paradox.LawExpr.noConfusion,
 Paradox.LawExpr.noConfusionType,
 Paradox.LawExpr.sign,
 Paradox.LawQuantity.value,
 Paradox.PortalEffect.Safe,
 Paradox.PortalEffect.apply,
 Paradox.Property.all,
 Paradox.Property.holds,
 Paradox.Property.name,
 Paradox.Rule.certified,
 Paradox.Rule.ctorElim,
 Paradox.Rule.ctorElimType,
 Paradox.Rule.envSafe,
 Paradox.Rule.establishes,
 Paradox.Rule.eval,
 Paradox.Rule.keeps,
 Paradox.Rule.noConfusion,
 Paradox.Rule.noConfusionType,
 Paradox.Shape.extent,
 Paradox.Vec3.WithinAbs,
 Paradox.Vec3.add,
 Paradox.Vec3.clampAbs,
 Paradox.Vec3.cross,
 Paradox.Vec3.dot,
 Paradox.Vec3.neg,
 Paradox.Vec3.scale,
 Paradox.Vec3.snap,
 Paradox.Vec3.sub,
 Paradox.Vec3.zero,
 Paradox.WorldAction.apply,
 Paradox.WorldAction.keeps,
 Paradox.WorldCond.ctorElim,
 Paradox.WorldCond.ctorElimType,
 Paradox.WorldCond.noConfusion,
 Paradox.WorldCond.noConfusionType,
 Paradox.WorldCond.test,
 Paradox.BodyAction.applyForce.elim,
 Paradox.BodyAction.clampPosition.elim,
 Paradox.BodyAction.clampVelocity.elim,
 Paradox.BodyAction.reverseVelocity.elim,
 Paradox.BodyAction.rotateVelocity.elim,
 Paradox.BodyAction.scaleMass.elim,
 Paradox.BodyAction.scaleVelocity.elim,
 Paradox.BodyAction.setCharge.elim,
 Paradox.BodyAction.setMassFormula.elim,
 Paradox.BodyAction.translate.elim,
 Paradox.BodyCond.all.elim,
 Paradox.BodyCond.entersBox.elim,
 Paradox.BodyCond.entersBox.noConfusion,
 Paradox.BodyCond.inBox.elim,
 Paradox.BodyCond.inBox.noConfusion,
 Paradox.BodyCond.inRegion.elim,
 Paradox.BodyCond.inRegion.noConfusion,
 Paradox.BodyCond.not.elim,
 Paradox.BodyCond.not.noConfusion,
 Paradox.BodyCond.onColor.elim,
 Paradox.BodyCond.onColor.noConfusion,
 Paradox.BodyCond.speedAbove.elim,
 Paradox.BodyCond.speedAbove.noConfusion,
 Paradox.Engine.Trace.final,
 Paradox.EnvironmentEvent.addField.elim,
 Paradox.EnvironmentEvent.addPortal.elim,
 Paradox.EnvironmentEvent.addRegion.elim,
 Paradox.EnvironmentEvent.addRule.elim,
 Paradox.EnvironmentEvent.applyImpulse.elim,
 Paradox.EnvironmentEvent.changeBounds.elim,
 Paradox.EnvironmentEvent.changeGravity.elim,
 Paradox.EnvironmentEvent.changeMaxAcceleration.elim,
 Paradox.EnvironmentEvent.changeMaxSpeed.elim,
 Paradox.EnvironmentEvent.changeRestitution.elim,
 Paradox.EnvironmentEvent.changeTimeStep.elim,
 Paradox.EnvironmentEvent.clearFields.elim,
 Paradox.EnvironmentEvent.clearPortals.elim,
 Paradox.EnvironmentEvent.clearRegions.elim,
 Paradox.EnvironmentEvent.clearRules.elim,
 Paradox.EnvironmentEvent.disableGravity.elim,
 Paradox.EnvironmentEvent.idle.elim,
 Paradox.EnvironmentEvent.removeBody.elim,
 Paradox.EnvironmentEvent.reverseGravity.elim,
 Paradox.EnvironmentEvent.reverseTime.elim,
 Paradox.EnvironmentEvent.setBodyState.elim,
 Paradox.EnvironmentEvent.setCentral.elim,
 Paradox.EnvironmentEvent.setCollisions.elim,
 Paradox.EnvironmentEvent.setDrag.elim,
 Paradox.EnvironmentEvent.setGrid.elim,
 Paradox.EnvironmentEvent.setMagnetic.elim,
 Paradox.EnvironmentEvent.setMassRate.elim,
 Paradox.EnvironmentEvent.setMetric.elim,
 Paradox.EnvironmentEvent.setPairForce.elim,
 Paradox.EnvironmentEvent.setPopulationLimit.elim,
 Paradox.EnvironmentEvent.setReaction.elim,
 Paradox.EnvironmentEvent.setTopology.elim,
 Paradox.EnvironmentEvent.spawnBody.elim,
 Paradox.LawExpr.add.elim,
 Paradox.LawExpr.add.noConfusion,
 Paradox.LawExpr.chargeA.elim,
 Paradox.LawExpr.chargeB.elim,
 Paradox.LawExpr.const.elim,
 Paradox.LawExpr.const.noConfusion,
 Paradox.LawExpr.dist.elim,
 Paradox.LawExpr.distSquared.elim,
 Paradox.LawExpr.div.elim,
 Paradox.LawExpr.div.noConfusion,
 Paradox.LawExpr.massA.elim,
 Paradox.LawExpr.massB.elim,
 Paradox.LawExpr.mul.elim,
 Paradox.LawExpr.mul.noConfusion,
 Paradox.LawExpr.neg.elim,
 Paradox.LawExpr.neg.noConfusion,
 Paradox.LawExpr.pow.elim,
 Paradox.LawExpr.pow.noConfusion,
 Paradox.LawExpr.speedSquared.elim,
 Paradox.LawExpr.sub.elim,
 Paradox.LawExpr.sub.noConfusion,
 Paradox.Rule.body.elim,
 Paradox.Rule.body.noConfusion,
 Paradox.Rule.create.elim,
 Paradox.Rule.create.noConfusion,
 Paradox.Rule.destroy.elim,
 Paradox.Rule.destroy.noConfusion,
 Paradox.Rule.seq.elim,
 Paradox.Rule.seq.noConfusion,
 Paradox.Rule.skip.elim,
 Paradox.Rule.when.elim,
 Paradox.Rule.when.noConfusion,
 Paradox.Rule.world.elim,
 Paradox.Rule.world.noConfusion,
 Paradox.WorldCond.always.elim,
 Paradox.WorldCond.everyTicks.elim,
 Paradox.WorldCond.everyTicks.noConfusion,
 Paradox.WorldCond.gravityAbove.elim,
 Paradox.WorldCond.gravityAbove.noConfusion,
 Paradox.WorldCond.gravityChanged.elim,
 Paradox.WorldCond.not.elim,
 Paradox.WorldCond.not.noConfusion]
-/
#guard_msgs in #spec_surface verifyProperty_proven

/--
info: [Paradox.Allowed,
 Paradox.Body,
 Paradox.BodyAction,
 Paradox.BodyAllowed,
 Paradox.BodyCond,
 Paradox.BodyQuantity,
 Paradox.BoundedPosition,
 Paradox.BoundedVelocity,
 Paradox.Bounds,
 Paradox.CanCreate,
 Paradox.Claim,
 Paradox.Cmp,
 Paradox.CollisionMode,
 Paradox.Constraint,
 Paradox.EnvironmentEvent,
 Paradox.EventScope,
 Paradox.Field,
 Paradox.FitsIn,
 Paradox.InScope,
 Paradox.LawExpr,
 Paradox.LawInputs,
 Paradox.LawQuantity,
 Paradox.Metric,
 Paradox.PhysicsLaws,
 Paradox.Portal,
 Paradox.PortalEffect,
 Paradox.PositiveMass,
 Paradox.Property,
 Paradox.Region,
 Paradox.Rule,
 Paradox.SafeEnvironment,
 Paradox.Shape,
 Paradox.Topology,
 Paradox.Touching,
 Paradox.UniqueIds,
 Paradox.Vec3,
 Paradox.World,
 Paradox.WorldAction,
 Paradox.WorldCond,
 Paradox.WorldTrace,
 Paradox.accelerate,
 Paradox.applyEvent,
 Paradox.applyForces,
 Paradox.approxSqrt,
 Paradox.bouncePair,
 Paradox.checkTrace,
 Paradox.childOf,
 Paradox.clamp,
 Paradox.clampAbs,
 Paradox.collisionStage,
 Paradox.evalRules,
 Paradox.exchangeMassPair,
 Paradox.exchangeVelocityPair,
 Paradox.externalAcceleration,
 Paradox.firstTouchingPair,
 Paradox.forcePair,
 Paradox.kineticEnergy,
 Paradox.limitSpeed,
 Paradox.mergeAll,
 Paradox.mergeBodies,
 Paradox.mergeOne,
 Paradox.metricSquared,
 Paradox.momentumAlong,
 Paradox.moveAxis,
 Paradox.moveBody,
 Paradox.pairAll,
 Paradox.pairInputs,
 Paradox.pairOne,
 Paradox.portalAt,
 Paradox.ruleInputs,
 Paradox.run,
 Paradox.selfInputs,
 Paradox.snap,
 Paradox.spawnStage,
 Paradox.step,
 Paradox.throughPortals,
 Paradox.tick,
 Paradox.timeScaleAt,
 Paradox.total,
 Paradox.totalEnergy,
 Paradox.totalMass,
 Paradox.totalMomentum,
 Paradox.updateBody,
 Paradox.withLaws,
 Paradox.wrap,
 Paradox.Body.extent,
 Paradox.BodyAction.apply,
 Paradox.BodyAction.ctorElim,
 Paradox.BodyAction.ctorElimType,
 Paradox.BodyAction.keeps,
 Paradox.BodyCond.ctorElim,
 Paradox.BodyCond.ctorElimType,
 Paradox.BodyCond.noConfusion,
 Paradox.BodyCond.noConfusionType,
 Paradox.BodyCond.test,
 Paradox.BodyQuantity.value,
 Paradox.Bounds.Contains,
 Paradox.Bounds.Valid,
 Paradox.Bounds.clampPoint,
 Paradox.Bounds.inset,
 Paradox.Claim.holds,
 Paradox.Cmp.holds,
 Paradox.Constraint.holds,
 Paradox.Engine.AllowedTrace,
 Paradox.Engine.Trace,
 Paradox.Engine.statesOf,
 Paradox.EnvironmentEvent.ctorElim,
 Paradox.EnvironmentEvent.ctorElimType,
 Paradox.LawExpr.ctorElim,
 Paradox.LawExpr.ctorElimType,
 Paradox.LawExpr.eval,
 Paradox.LawExpr.noConfusion,
 Paradox.LawExpr.noConfusionType,
 Paradox.LawExpr.sign,
 Paradox.LawQuantity.value,
 Paradox.PortalEffect.Safe,
 Paradox.PortalEffect.apply,
 Paradox.Property.all,
 Paradox.Property.holds,
 Paradox.Rule.certified,
 Paradox.Rule.ctorElim,
 Paradox.Rule.ctorElimType,
 Paradox.Rule.envSafe,
 Paradox.Rule.establishes,
 Paradox.Rule.eval,
 Paradox.Rule.keeps,
 Paradox.Rule.noConfusion,
 Paradox.Rule.noConfusionType,
 Paradox.Shape.extent,
 Paradox.Vec3.WithinAbs,
 Paradox.Vec3.add,
 Paradox.Vec3.clampAbs,
 Paradox.Vec3.cross,
 Paradox.Vec3.dot,
 Paradox.Vec3.neg,
 Paradox.Vec3.scale,
 Paradox.Vec3.snap,
 Paradox.Vec3.sub,
 Paradox.Vec3.zero,
 Paradox.WorldAction.apply,
 Paradox.WorldAction.keeps,
 Paradox.WorldCond.ctorElim,
 Paradox.WorldCond.ctorElimType,
 Paradox.WorldCond.noConfusion,
 Paradox.WorldCond.noConfusionType,
 Paradox.WorldCond.test,
 Paradox.BodyAction.applyForce.elim,
 Paradox.BodyAction.clampPosition.elim,
 Paradox.BodyAction.clampVelocity.elim,
 Paradox.BodyAction.reverseVelocity.elim,
 Paradox.BodyAction.rotateVelocity.elim,
 Paradox.BodyAction.scaleMass.elim,
 Paradox.BodyAction.scaleVelocity.elim,
 Paradox.BodyAction.setCharge.elim,
 Paradox.BodyAction.setMassFormula.elim,
 Paradox.BodyAction.translate.elim,
 Paradox.BodyCond.all.elim,
 Paradox.BodyCond.entersBox.elim,
 Paradox.BodyCond.entersBox.noConfusion,
 Paradox.BodyCond.inBox.elim,
 Paradox.BodyCond.inBox.noConfusion,
 Paradox.BodyCond.inRegion.elim,
 Paradox.BodyCond.inRegion.noConfusion,
 Paradox.BodyCond.not.elim,
 Paradox.BodyCond.not.noConfusion,
 Paradox.BodyCond.onColor.elim,
 Paradox.BodyCond.onColor.noConfusion,
 Paradox.BodyCond.speedAbove.elim,
 Paradox.BodyCond.speedAbove.noConfusion,
 Paradox.Engine.Trace.final,
 Paradox.EnvironmentEvent.addField.elim,
 Paradox.EnvironmentEvent.addPortal.elim,
 Paradox.EnvironmentEvent.addRegion.elim,
 Paradox.EnvironmentEvent.addRule.elim,
 Paradox.EnvironmentEvent.applyImpulse.elim,
 Paradox.EnvironmentEvent.changeBounds.elim,
 Paradox.EnvironmentEvent.changeGravity.elim,
 Paradox.EnvironmentEvent.changeMaxAcceleration.elim,
 Paradox.EnvironmentEvent.changeMaxSpeed.elim,
 Paradox.EnvironmentEvent.changeRestitution.elim,
 Paradox.EnvironmentEvent.changeTimeStep.elim,
 Paradox.EnvironmentEvent.clearFields.elim,
 Paradox.EnvironmentEvent.clearPortals.elim,
 Paradox.EnvironmentEvent.clearRegions.elim,
 Paradox.EnvironmentEvent.clearRules.elim,
 Paradox.EnvironmentEvent.disableGravity.elim,
 Paradox.EnvironmentEvent.idle.elim,
 Paradox.EnvironmentEvent.removeBody.elim,
 Paradox.EnvironmentEvent.reverseGravity.elim,
 Paradox.EnvironmentEvent.reverseTime.elim,
 Paradox.EnvironmentEvent.setBodyState.elim,
 Paradox.EnvironmentEvent.setCentral.elim,
 Paradox.EnvironmentEvent.setCollisions.elim,
 Paradox.EnvironmentEvent.setDrag.elim,
 Paradox.EnvironmentEvent.setGrid.elim,
 Paradox.EnvironmentEvent.setMagnetic.elim,
 Paradox.EnvironmentEvent.setMassRate.elim,
 Paradox.EnvironmentEvent.setMetric.elim,
 Paradox.EnvironmentEvent.setPairForce.elim,
 Paradox.EnvironmentEvent.setPopulationLimit.elim,
 Paradox.EnvironmentEvent.setReaction.elim,
 Paradox.EnvironmentEvent.setTopology.elim,
 Paradox.EnvironmentEvent.spawnBody.elim,
 Paradox.LawExpr.add.elim,
 Paradox.LawExpr.add.noConfusion,
 Paradox.LawExpr.chargeA.elim,
 Paradox.LawExpr.chargeB.elim,
 Paradox.LawExpr.const.elim,
 Paradox.LawExpr.const.noConfusion,
 Paradox.LawExpr.dist.elim,
 Paradox.LawExpr.distSquared.elim,
 Paradox.LawExpr.div.elim,
 Paradox.LawExpr.div.noConfusion,
 Paradox.LawExpr.massA.elim,
 Paradox.LawExpr.massB.elim,
 Paradox.LawExpr.mul.elim,
 Paradox.LawExpr.mul.noConfusion,
 Paradox.LawExpr.neg.elim,
 Paradox.LawExpr.neg.noConfusion,
 Paradox.LawExpr.pow.elim,
 Paradox.LawExpr.pow.noConfusion,
 Paradox.LawExpr.speedSquared.elim,
 Paradox.LawExpr.sub.elim,
 Paradox.LawExpr.sub.noConfusion,
 Paradox.Rule.body.elim,
 Paradox.Rule.body.noConfusion,
 Paradox.Rule.create.elim,
 Paradox.Rule.create.noConfusion,
 Paradox.Rule.destroy.elim,
 Paradox.Rule.destroy.noConfusion,
 Paradox.Rule.seq.elim,
 Paradox.Rule.seq.noConfusion,
 Paradox.Rule.skip.elim,
 Paradox.Rule.when.elim,
 Paradox.Rule.when.noConfusion,
 Paradox.Rule.world.elim,
 Paradox.Rule.world.noConfusion,
 Paradox.WorldCond.always.elim,
 Paradox.WorldCond.everyTicks.elim,
 Paradox.WorldCond.everyTicks.noConfusion,
 Paradox.WorldCond.gravityAbove.elim,
 Paradox.WorldCond.gravityAbove.noConfusion,
 Paradox.WorldCond.gravityChanged.elim,
 Paradox.WorldCond.not.elim,
 Paradox.WorldCond.not.noConfusion]
-/
#guard_msgs in #spec_surface checkTrace_sound

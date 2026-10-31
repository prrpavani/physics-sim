import Lean
import Paradox.Verification.Examples

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
      !isRecCore env c && !isCasesOnRecursor env c && c.getString! != "ctorIdx"
  logInfo m!"{(own.qsort Name.lt).toList}"

end Paradox.Audit

open Paradox

/-! ## Axioms -/

/-- info: 'Paradox.guaranteed_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms guaranteed_run

/-- info: 'Paradox.guaranteed_preservesAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms guaranteed_preservesAll

/-- info: 'Paradox.run_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_preserves

/-- info: 'Paradox.step_preserves_positiveMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_preserves_positiveMass

/-- info: 'Paradox.step_preserves_boundedPosition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_preserves_boundedPosition

/-- info: 'Paradox.boundedVelocity_preservesAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boundedVelocity_preservesAll

/-- info: 'Paradox.safeEnvironment_preservesAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms safeEnvironment_preservesAll

/-- info: 'Paradox.negative_maxSpeed_violates_boundedVelocity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms negative_maxSpeed_violates_boundedVelocity

/-- info: 'Paradox.demoWorld_guaranteed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms demoWorld_guaranteed

/-! ## Trusted surface -/

/--
info: [Paradox.Allowed,
 Paradox.AllowedTrace,
 Paradox.Body,
 Paradox.BoundedPosition,
 Paradox.BoundedVelocity,
 Paradox.Bounds,
 Paradox.EnvironmentEvent,
 Paradox.Guaranteed,
 Paradox.PhysicsLaws,
 Paradox.PositiveMass,
 Paradox.SafeEnvironment,
 Paradox.Vec3,
 Paradox.World,
 Paradox.applyEvent,
 Paradox.clamp,
 Paradox.clampAbs,
 Paradox.run,
 Paradox.step,
 Paradox.tick,
 Paradox.tickBody,
 Paradox.Bounds.Contains,
 Paradox.Bounds.Valid,
 Paradox.Bounds.clampPoint,
 Paradox.EnvironmentEvent.applyToLaws,
 Paradox.Vec3.WithinAbs,
 Paradox.Vec3.add,
 Paradox.Vec3.clampAbs,
 Paradox.Vec3.neg,
 Paradox.Vec3.scale,
 Paradox.Vec3.zero]
-/
#guard_msgs in #spec_surface guaranteed_run

/--
info: [Paradox.Body,
 Paradox.BoundedVelocity,
 Paradox.Bounds,
 Paradox.EnvironmentEvent,
 Paradox.PhysicsLaws,
 Paradox.Vec3,
 Paradox.World,
 Paradox.applyEvent,
 Paradox.clamp,
 Paradox.clampAbs,
 Paradox.step,
 Paradox.tick,
 Paradox.tickBody,
 Paradox.Bounds.clampPoint,
 Paradox.EnvironmentEvent.applyToLaws,
 Paradox.Vec3.WithinAbs,
 Paradox.Vec3.add,
 Paradox.Vec3.clampAbs,
 Paradox.Vec3.neg,
 Paradox.Vec3.scale,
 Paradox.Vec3.zero]
-/
#guard_msgs in #spec_surface negative_maxSpeed_violates_boundedVelocity

// Plain-language text for rules, formulas, events and claims.

import type {
  BodyAction, BodyCond, Claim, Constraint, EnvironmentEvent, LawExpr, Property, Rule, Status, Vec3, WorldAction, WorldCond,
} from "../../../../shared/types/paradox";
import { showNum } from "./num";

const v3 = (v: Vec3) => `(${showNum(v.x)}, ${showNum(v.y)}, ${showNum(v.z)})`;

export function formula(e: LawExpr): string {
  switch (e.type) {
    case "const": return showNum(e.value, 3);
    case "massA": return "m₁";
    case "massB": return "m₂";
    case "chargeA": return "q₁";
    case "chargeB": return "q₂";
    case "distSquared": return "r²";
    case "dist": return "r";
    case "speedSquared": return "v²";
    case "add": return `${formula(e.a)} + ${formula(e.b)}`;
    case "sub": return `${formula(e.a)} − ${wrap(e.b)}`;
    case "mul": return `${wrap(e.a)} · ${wrap(e.b)}`;
    case "div": return `${wrap(e.a)} / ${wrap(e.b)}`;
    case "neg": return `−${wrap(e.a)}`;
    case "pow": return `${wrap(e.a)}^${e.n}`;
  }
}

function wrap(e: LawExpr): string {
  return e.type === "add" || e.type === "sub" ? `(${formula(e)})` : formula(e);
}

function bodyCond(c: BodyCond): string {
  switch (c.type) {
    case "all": return "every object";
    case "inBox": return "objects inside a zone";
    case "entersBox": return "objects entering a zone";
    case "inRegion": return `objects in “${c.name}”`;
    case "onColor": return `objects on ${c.color}`;
    case "speedAbove": return `objects faster than ${showNum(c.speed)}`;
    case "not": return `objects that are not: ${bodyCond(c.condition)}`;
  }
}

function bodyAction(a: BodyAction): string {
  switch (a.type) {
    case "applyForce": return `push with force ${v3(a.force)}`;
    case "reverseVelocity": return "reverse velocity";
    case "rotateVelocity": return "turn velocity a quarter turn";
    case "scaleVelocity": return `multiply velocity by ${showNum(a.factor)}`;
    case "clampVelocity": return "limit velocity to the speed limit";
    case "translate": return `teleport by ${v3(a.by)}`;
    case "clampPosition": return "bring back inside the world";
    case "scaleMass": return `multiply mass by ${showNum(a.factor)}`;
    case "setMassFormula": return `set mass to ${formula(a.formula)}`;
    case "setCharge": return `set charge to ${showNum(a.charge)}`;
  }
}

function worldCond(c: WorldCond): string {
  switch (c.type) {
    case "always": return "always";
    case "gravityAbove": return `gravity is above ${showNum(c.value)}`;
    case "gravityChanged": return "gravity changes";
    case "everyTicks": return `every ${c.n} steps`;
    case "not": return `not (${worldCond(c.condition)})`;
  }
}

function worldAction(a: WorldAction): string {
  switch (a.type) {
    case "setGravity": return `set gravity to ${v3(a.gravity)}`;
    case "reverseGravity": return "reverse gravity";
    case "setMaxSpeed": return `set the speed limit to ${showNum(a.value)}`;
    case "setPairForce": return `set the force law to ${formula(a.formula)}`;
    case "setReaction": return `set the reaction factor to ${showNum(a.value)}`;
    case "setMassRate": return `set the mass rate to ${showNum(a.value)}`;
  }
}

export function rule(r: Rule): string {
  switch (r.type) {
    case "skip": return "do nothing";
    case "body": return `${bodyAction(r.action)} for ${bodyCond(r.condition ?? { type: "all" })}`;
    case "world": return worldAction(r.action);
    case "destroy": return `destroy ${bodyCond(r.condition)}`;
    case "create": return "create a new object";
    case "seq": return `${rule(r.first)}, then ${rule(r.then)}`;
    case "when": return `when ${worldCond(r.condition)}: ${rule(r.rule)}`;
  }
}

/** An event as a request. It may have been refused, so it does not say the change happened. */
export function event(e: EnvironmentEvent): string {
  switch (e.type) {
    case "idle": return "Let time pass";
    case "reverseGravity": return "Reverse gravity";
    case "disableGravity": return "Switch off gravity";
    case "clearFields": return "Remove all fields";
    case "reverseTime": return "Reverse time";
    case "clearRegions": return "Remove all regions";
    case "clearPortals": return "Remove all portals";
    case "clearRules": return "Remove all rules";
    case "changeGravity": return `Set gravity to ${v3(e.gravity)}`;
    case "changeMaxSpeed": return `Set the speed limit to ${showNum(e.value)}`;
    case "changeMaxAcceleration": return `Set the acceleration limit to ${showNum(e.value)}`;
    case "changeRestitution": return `Set bounciness to ${showNum(e.value)}`;
    case "changeTimeStep": return `Set the time step to ${showNum(e.value, 3)}`;
    case "setReaction": return `Set the reaction factor to ${showNum(e.value)}`;
    case "setMassRate": return `Set the mass rate to ${showNum(e.value, 3)}`;
    case "changeBounds": return "Change the world boundary";
    case "addField": return "Add a field";
    case "setPairForce": return `Set the force law to ${formula(e.formula)}`;
    case "setDrag": return `Set drag to ${formula(e.formula)}`;
    case "setCentral": return `Set the central force to ${formula(e.formula)}`;
    case "setMagnetic": return `Set the magnetic field to ${v3(e.field)}`;
    case "setTopology": return e.topology === "torus" ? "Make space loop" : "Give space walls";
    case "setMetric": return `Measure distance by ${e.metric}`;
    case "setCollisions": return `Set collisions to ${e.mode}`;
    case "setPopulationLimit": return `Set the population limit to ${e.value}`;
    case "setGrid": return `Set the grid to 1/${e.value}`;
    case "spawnBody": return `Add object ${e.body.id}`;
    case "removeBody": return `Remove object ${e.id}`;
    case "applyImpulse": return `Push object ${e.id} by ${v3(e.impulse)}`;
    case "setBodyState": return `Move object ${e.id}`;
    case "addRegion": return `Add region “${e.region.name}”`;
    case "addPortal": return "Add a portal";
    case "addRule": return `Add rule: ${rule(e.rule)}`;
  }
}

export const propertyName: Record<Property, string> = {
  positiveMass: "Positive mass",
  boundedPosition: "Stays inside the world",
  boundedVelocity: "Speed limit",
  safeEnvironment: "Safe environment",
  uniqueIds: "Unique objects",
};

export const propertyMeaning: Record<Property, string> = {
  positiveMass: "Every object has mass above zero.",
  boundedPosition: "Every object is fully inside the world.",
  boundedVelocity: "Every velocity component is within the speed limit.",
  safeEnvironment: "The laws are meaningful, and every object fits in the world.",
  uniqueIds: "No two objects share an id.",
};

const quantityName: Record<string, string> = {
  mass: "mass", charge: "charge", extent: "size",
  positionX: "x position", positionY: "y position", positionZ: "z position",
  velocityX: "x velocity", velocityY: "y velocity", velocityZ: "z velocity",
  speedSquared: "speed²",
  gravityX: "gravity x", gravityY: "gravity y", gravityZ: "gravity z",
  maxSpeed: "speed limit", maxAcceleration: "acceleration limit", restitution: "bounciness",
  timeStep: "time step", massRate: "mass rate", reaction: "reaction factor",
};
const cmpName = { lt: "<", le: "≤", eq: "=", ge: "≥", gt: ">" };

export function constraint(c: Constraint): string {
  const tail = `${cmpName[c.cmp]} ${showNum(c.value)}`;
  switch (c.type) {
    case "body": return `Every object: ${quantityName[c.quantity]} ${tail}`;
    case "population": return `Number of objects ${tail}`;
    case "law": return `Law: ${quantityName[c.quantity]} ${tail}`;
  }
}

export function claim(c: Claim): string {
  if (typeof c === "string") return propertyName[c];
  switch (c.type) {
    case "property": return propertyName[c.property];
    case "constraint": return constraint(c.constraint);
    case "momentumConserved": return `Momentum conserved along ${v3(c.direction)}`;
    case "energyNotRising": return "Energy never rises";
    case "massConserved": return "Mass conserved";
    case "populationConserved": return "Population constant";
  }
}

export const statusLabel: Record<Status, string> = {
  proven: "Proven",
  counterexample: "Counterexample",
  unknown: "Unproven",
  underspecified: "Underspecified",
  inconsistent: "Contradiction",
};

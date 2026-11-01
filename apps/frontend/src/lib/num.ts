// Rational strings are the exact values. These helpers convert for drawing and for slider input.
// Nothing here is used to decide what happens in a universe.

import type { Bounds, Vec3 } from "../../../../shared/types/paradox";

export function num(r: string | number | null | undefined): number {
  if (r === null || r === undefined) return 0;
  if (typeof r === "number") return r;
  const parts = r.split("/");
  if (parts.length === 2) return Number(parts[0]) / Number(parts[1]);
  return Number(r);
}

/** A number as an exact rational string, to a useful precision. */
export function frac(x: number, den = 1000): string {
  const n = Math.round(x * den);
  if (n % den === 0) return String(n / den);
  const g = gcd(Math.abs(n), den);
  return `${n / g}/${den / g}`;
}

function gcd(a: number, b: number): number {
  return b === 0 ? a : gcd(b, a % b);
}

export const vec = (x: number, y: number, z: number): Vec3 => ({ x: frac(x), y: frac(y), z: frac(z) });
export const vecNums = (v: Vec3): [number, number, number] => [num(v.x), num(v.y), num(v.z)];

export const boundsAround = (cx: number, cy: number, cz: number, size: number): Bounds => ({
  minX: frac(cx - size), maxX: frac(cx + size),
  minY: frac(cy - size), maxY: frac(cy + size),
  minZ: frac(cz - size), maxZ: frac(cz + size),
});

export function showNum(r: string | number, digits = 2): string {
  const x = num(r);
  if (!Number.isFinite(x)) return "—";
  if (Number.isInteger(x)) return String(x);
  return x.toFixed(digits);
}

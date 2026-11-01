// Rational strings are the exact values. These helpers convert for the sliders and for drawing only.

export function num(r: string): number {
  const parts = r.split("/");
  return parts.length === 2 ? Number(parts[0]) / Number(parts[1]) : Number(r);
}

/** A slider value as an exact rational string. */
export function frac(x: number): string {
  const n = Math.round(x * 1000);
  if (n % 1000 === 0) return String(n / 1000);
  const gcd = (a: number, b: number): number => (b === 0 ? a : gcd(b, a % b));
  const g = gcd(Math.abs(n), 1000);
  return `${n / g}/${1000 / g}`;
}

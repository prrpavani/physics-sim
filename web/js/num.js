// Exact numbers travel as strings: "-981/100" or "20". The browser turns them into decimals for
// drawing only, and turns slider values into fractions with denominator 1000 before sending them.

export function toNum(s) {
  const [p, q] = String(s).split("/");
  return q === undefined ? Number(p) : Number(p) / Number(q);
}

const gcd = (a, b) => (b === 0 ? Math.abs(a) : gcd(b, a % b));

export function toFrac(x, denom = 1000) {
  const n = Math.round(x * denom);
  const g = gcd(n, denom) || 1;
  return denom / g === 1 ? String(n / g) : `${n / g}/${denom / g}`;
}

export const vecNum = v => v.map(toNum);
export const vecFrac = v => v.map(x => toFrac(x));

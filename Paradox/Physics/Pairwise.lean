import Paradox.Core.Body

/-!
# Applying an interaction to every pair of bodies

Collisions and invented forces both act on two bodies at a time. They share this one traversal, so
the facts proved about it apply to both.
-/

namespace Paradox

/-- Apply `f` to `a` and each body in the list in turn. -/
def pairOne (f : Body → Body → Body × Body) (a : Body) : List Body → Body × List Body
  | [] => (a, [])
  | c :: cs =>
    let p := f a c
    let r := pairOne f p.1 cs
    (r.1, p.2 :: r.2)

/-- Apply `f` to every pair of bodies in the list once. -/
def pairAll (f : Body → Body → Body × Body) : List Body → List Body
  | [] => []
  | b :: bs =>
    let r := pairOne f b (pairAll f bs)
    r.1 :: r.2

end Paradox

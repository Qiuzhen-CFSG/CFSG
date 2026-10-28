module

public import Mathlib.Data.Nat.Basic

/-!
# Sharpness in the dihedral induction

In G.9.2, write `m = k+n+1` and `d = dim U + 2 dim W` after splitting off
the last dihedral factor. The sharp upper bound permits either no factors
on `W`, with `dim W=1`, or one cubic factor, with `dim W=2`.
An exceptional factor acting on `W` would exceed that upper bound.

These arithmetic implications do not supply the invariant subspaces or
their faithful actions. Those are the representation-theoretic induction
obligations. Source: Aschbacher--Smith G.9.2, printed pp.352--353.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity

/-- Once the exceptional factor lies on `U`, the dimension inequalities
force equality and at most one factor acting on `W`. The parameter `e`
counts the exceptional contribution and is zero or one in the application. -/
theorem split_dimensions_rigid {d m k n u w e : ℕ}
    (hrank : m = k + n + 1) (hdim : d = u + 2 * w)
    (hupper : d ≤ 2 * (m + e)) (hU : 2 * (k + e) ≤ u)
    (hW : 2 * n ≤ w) (hWpos : 1 ≤ w) :
    d = 2 * (m + e) ∧ u = 2 * (k + e) ∧ n ≤ 1 ∧
      ((n = 0 ∧ w = 1) ∨ (n = 1 ∧ w = 2)) := by
  omega

/-- The exceptional prime cannot occur in the product acting faithfully
on the half-space `W`. In particular the rank in its lower bound is `n`,
not the `m` printed in the sentence labelled (J2). -/
theorem exceptional_half_space_impossible {d m k n u w : ℕ}
    (hrank : m = k + n + 1) (hdim : d = u + 2 * w)
    (hupper : d ≤ 2 * (m + 1)) (hU : 2 * k ≤ u)
    (hW : 2 * (n + 1) ≤ w) (hn : 0 < n) : False := by
  omega

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity

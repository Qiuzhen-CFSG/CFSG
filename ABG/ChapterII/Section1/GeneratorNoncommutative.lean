module

public import Theory.GroupTheory.SemidihedralCenter
public import Stellmacher.MainDefs

/-!
# The quasi-dihedral generators do not commute

For the presentation of ABG Chapter I, article page 2, the cyclic generator
has order `2^(n-1)` and conjugation raises it to `2^(n-2)-1`, where `n ≥ 4`.
These data alone force the two generators not to commute: otherwise the
first power and that conjugate power agree, although their exponents are
distinct and strictly below the order. This explicit form is used both for
noncommutativity of the group and for its center calculation. The reusable
proof now lives in `Theory.GroupTheory.SemidihedralCenter`; this module
preserves the original ABG name and statement as a forwarding theorem.
-/

namespace ABG.QuasiDihedral

/-- The cyclic and involutory generators in the quasi-dihedral presentation
do not commute; only the cyclic generator order and conjugation are needed. -/
public theorem generators_not_commute {S : Type*} [Group S] {n : ℕ} (hn : 4 ≤ n)
    {a b : S} (ha : orderOf a = 2 ^ (n - 1))
    (hab : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1)) : ¬ Commute a b :=
  Semidihedral.generators_not_commute hn ha hab

end ABG.QuasiDihedral

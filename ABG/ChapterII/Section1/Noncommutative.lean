module

public import ABG.ChapterII.Section1.GeneratorNoncommutative

/-!
# Quasi-dihedral groups are noncommutative

The quasi-dihedral presentation in ABG Chapter I, article page 2, is
`Stellmacher.IsSemidihedralGroup`, with the exponent parameter shifted by one.
Its cyclic generator has order `2^(n-1)` for `n ≥ 4`, and conjugation by the
involutory generator raises it to `2^(n-2)-1`. If the group were commutative,
these would equal the first power, contradicting distinct exponents below the
generator order. This elementary observation supports the simple-group
reductions used with Chapter II, Section 1.
-/

namespace ABG.QuasiDihedral

/-- A group with the quasi-dihedral presentation is not commutative. -/
public theorem not_isMulCommutative {S : Type*} [Group S] (hS : Stellmacher.IsSemidihedralGroup S) :
    ¬ IsMulCommutative S := by
  rintro hcomm
  let := hcomm
  obtain ⟨n, hn, _, a, b, ha, _, hab, _⟩ := hS
  exact generators_not_commute hn ha hab (show Commute a b from mul_comm' a b)

end ABG.QuasiDihedral

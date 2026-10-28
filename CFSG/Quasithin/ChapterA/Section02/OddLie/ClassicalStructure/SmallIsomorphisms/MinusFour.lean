module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison

/-!
# The minus-four comparison and the low-rank boundary

The actual minus-four scalar quotient over a field of order q is PSL₂ over
a field of order q². Transport through the original model isomorphism gives
the corresponding model predicate with the squared cardinality preserved.
Thus the earlier PSL₂ branch removes the four-dimensional minus case.

Both truncated ranks have abelian commutator/scalar quotients in odd
characteristic, so nonabelianity excludes them. These results justify the
minus-rank lower boundary used in the small orthogonal reduction in
Aschbacher–Smith A.2.17, printed pp.38–39 (`refs/quasithin.pdf`), with the
minus carrier conventions of GLS3 §2.7.
-/

public section

namespace CFSG.Quasithin.ChapterA.Section02.SmallIsomorphisms
open ClassicalGroup
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] {r q : ℕ}

/-- The minus-four model belongs to the PSL₂ branch over the field of order q². -/
theorem isPSL_two_sq_of_isPOmegaMinus_two (h : IsPOmegaMinus G 2 q) :
    IsPSL G 2 (q ^ 2) := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  obtain ⟨E, hE, hEfin, hcard, ⟨f⟩⟩ :=
    ClassicalOrthogonal.Minus.OddFourComparison.exists_projectiveEquivPSL F
  exact ⟨E, hE, hEfin, hcard.trans (by rw [hc]), ⟨e.trans f⟩⟩

/-- Nonabelianity excludes the two truncated minus ranks, retaining the original field witness. -/
theorem orthogonalMinus_rank_ge_two (ho : Odd q) (hnab : ¬ IsMulCommutative G)
    (h : IsPOmegaMinus G r q) : 2 ≤ r := by
  by_contra hr
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  let := ClassicalOrthogonal.Minus.OddFourComparison.LowRanks.pOmegaMinus_commutative_of_le_one_odd
    F (by simpa only [hc] using ho) r (by omega)
  apply hnab
  apply IsMulCommutative.of_comm
  intro x y
  apply e.injective
  simp only [map_mul, mul_comm]

/-- After the earlier PSL₂ branch, a nonabelian odd minus model has rank at least three. -/
theorem orthogonalMinus_rank_ge_three (ho : Odd q) (hnab : ¬ IsMulCommutative G)
    (hnot : ¬ IsPSL G 2 (q ^ 2)) (h : IsPOmegaMinus G r q) : 3 ≤ r := by
  have hr := orthogonalMinus_rank_ge_two ho hnab h
  have hne : r ≠ 2 := by
    intro he
    subst r
    exact hnot (isPSL_two_sq_of_isPOmegaMinus_two h)
  omega

end CFSG.Quasithin.ChapterA.Section02.SmallIsomorphisms

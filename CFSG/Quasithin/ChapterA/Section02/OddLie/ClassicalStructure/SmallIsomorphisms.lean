module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.ClassicalMatrixLowRanks
public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer.RankOne
public import Theory.SpecificGroups.ClassicalUnitary.OddRankOneComparison
public import Theory.SpecificGroups.ClassicalOrthogonal.RankOneComparison.Comparison
public import Theory.SpecificGroups.ClassicalOrthogonal.SourcePredicateLowRanks
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitFourComparison

/-!
# Small classical comparisons for the odd-characteristic reduction

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), A.2.17, printed pp.38–39; GLS3 §2.7.

The genuine PSU₂, PSp₂ and PΩ₃ comparisons put their model predicates into
the previously treated PSL₂ branch. The unitary construction uses the actual
fixed subfield of the stored Hermitian conjugation and proves its order is q.
Triviality removes degenerate linear, unitary, symplectic and odd parameters.
The split-four determinant comparison gives two nontrivial PSL₂ factors, so
simplicity excludes this split orthogonal carrier over every field.

The resulting consumers justify linear/unitary dimension greater than two
and symplectic rank greater than one after the PSL₂ exclusion. The complete
orthogonal dimension-at-least-seven reduction additionally needs the odd-five,
split-six and minus-four/minus-six comparisons and the degenerate minus-plane
exclusion. Those remaining comparisons are not assumed or asserted here.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterA.Section02.SmallIsomorphisms
open ClassicalGroup
open ClassicalOrthogonal.SourcePredicateLowRanks

universe u
variable {G : Type u} [Group G] {q n r : ℕ}

/-- The unitary parameter is the order of the actual fixed field. -/
theorem isPSL_two_of_isPSU_two (hq : IsPrimePow q) (ho : Odd q)
    (h : IsPSU G 2 q) : IsPSL G 2 q := by
  obtain ⟨F, hF, hfin, J, hc, hj, ⟨e⟩⟩ := h
  obtain ⟨f⟩ := J.nonempty_projectiveTwoEquiv_odd hq ho hc hj
  refine ⟨FixedBy.subfield F J.conj, inferInstance, inferInstance, ?_, ⟨e.trans f⟩⟩
  exact J.fixed_card_prime_power hq hc hj

/-- Rank-one PSp is PSL₂ over the same coefficient field. -/
theorem isPSL_two_of_isPSp_one (h : IsPSp G 1 q) : IsPSL G 2 q := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  exact ⟨F, hF, hfin, hc,
    ⟨e.trans Theory.SpecificGroups.SymplecticRoot.rankOneProjectiveEquiv⟩⟩

/-- The actual elementary odd orthogonal group in dimension three is PSL₂. -/
theorem isPSL_two_of_isPOmegaOdd_one (h : IsPOmegaOdd G 1 q) : IsPSL G 2 q := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  exact ⟨F, hF, hfin, hc,
    ⟨e.trans ClassicalOrthogonal.RankOneComparison.projectiveEquivPSL⟩⟩

/-- Dimensions zero and one give trivial linear carriers. -/
theorem linear_dimension_ge_two [Nontrivial G] (h : IsPSL G n q) : 2 ≤ n := by
  by_contra hn
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  let := ClassicalMatrixLowRanks.psl_subsingleton F n (by omega)
  have : Subsingleton G := e.injective.subsingleton
  exact false_of_nontrivial_of_subsingleton G

/-- Every Hermitian form in dimension zero or one has trivial projective group. -/
theorem unitary_dimension_ge_two [Nontrivial G] (h : IsPSU G n q) : 2 ≤ n := by
  by_contra hn
  obtain ⟨F, hF, hfin, J, _, _, ⟨e⟩⟩ := h
  let := ClassicalMatrixLowRanks.psu_subsingleton F n (by omega) J
  have : Subsingleton G := e.injective.subsingleton
  exact false_of_nontrivial_of_subsingleton G

/-- The rank-zero symplectic carrier is trivial. -/
theorem symplectic_rank_pos [Nontrivial G] (h : IsPSp G r q) : 0 < r := by
  by_contra hr
  have hr0 : r = 0 := by omega
  subst r
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  let := ClassicalMatrixLowRanks.psp_zero_subsingleton F
  have : Subsingleton G := e.injective.subsingleton
  exact false_of_nontrivial_of_subsingleton G

/-- The odd orthogonal line has trivial elementary group. -/
theorem orthogonalOdd_rank_pos [Nontrivial G] (h : IsPOmegaOdd G r q) : 0 < r := by
  by_contra hr
  have hr0 : r = 0 := by omega
  subst r
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  let := pOmegaOdd_zero_subsingleton F
  have : Subsingleton G := e.injective.subsingleton
  exact false_of_nontrivial_of_subsingleton G

/-- Simplicity excludes split dimensions zero, two and the product in dimension four. -/
theorem orthogonalPlus_rank_ge_three [IsSimpleGroup G]
    (h : IsPOmegaPlus G r q) : 3 ≤ r := by
  by_contra hr
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  have hrsmall : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hrsmall with rfl | rfl | rfl
  · let := pOmegaPlus_zero_subsingleton F
    have : Subsingleton G := e.injective.subsingleton
    exact false_of_nontrivial_of_subsingleton G
  · let := pOmegaPlus_one_subsingleton F
    have : Subsingleton G := e.injective.subsingleton
    exact false_of_nontrivial_of_subsingleton G
  · exact ClassicalOrthogonal.FourPlusMatrix.not_isSimpleGroup_pOmegaPlus_two F
      e.symm.isSimpleGroup

/-- After the PSL₂ branch of A.2.17, the remaining linear dimension exceeds two. -/
theorem linear_dimension_gt_two [Nontrivial G]
    (hnot : ¬ IsPSL G 2 q) (h : IsPSL G n q) : 2 < n := by
  have hn := linear_dimension_ge_two h
  have hne : n ≠ 2 := by intro he; subst n; exact hnot h
  omega

/-- The fixed-field comparison removes PSU₂ in the same earlier PSL₂ branch. -/
theorem unitary_dimension_gt_two [Nontrivial G] (hq : IsPrimePow q) (ho : Odd q)
    (hnot : ¬ IsPSL G 2 q) (h : IsPSU G n q) : 2 < n := by
  have hn := unitary_dimension_ge_two h
  have hne : n ≠ 2 := by
    intro he
    subst n
    exact hnot (isPSL_two_of_isPSU_two hq ho h)
  omega

/-- The PSp₂ comparison justifies the source's symplectic rank restriction. -/
theorem symplectic_rank_gt_one [Nontrivial G]
    (hnot : ¬ IsPSL G 2 q) (h : IsPSp G r q) : 1 < r := by
  have hr := symplectic_rank_pos h
  have hne : r ≠ 1 := by
    intro he
    subst r
    exact hnot (isPSL_two_of_isPSp_one h)
  omega

/-- The dimension-three orthogonal alias belongs to the earlier PSL₂ branch. -/
theorem orthogonalOdd_rank_gt_one [Nontrivial G]
    (hnot : ¬ IsPSL G 2 q) (h : IsPOmegaOdd G r q) : 1 < r := by
  have hr := orthogonalOdd_rank_pos h
  have hne : r ≠ 1 := by
    intro he
    subst r
    exact hnot (isPSL_two_of_isPOmegaOdd_one h)
  omega

end CFSG.Quasithin.ChapterA.Section02.SmallIsomorphisms

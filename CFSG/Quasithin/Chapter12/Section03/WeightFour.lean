module

public import Theory.Representation.BinarySevenCode

/-!
# The weight-four plane in §12.3

In the proof of Lemma 12.3.9, printed p. 810, the plane spanned by
`e_{1,2,3,4}` and `e(4) = e_{3,4,5,6}` is asserted to be a maximal subspace
whose nonzero vectors have weight four. It is properly contained in the
three-dimensional simplex code: adjoining `e_{1,3,5,7}` preserves that property.
Consequently a proof of the asserted group-theoretic bound `r(G,V) ≥ 4`
must use more than the weight restriction on intersections.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript, 1 March 2004, §12.3.
-/

namespace CFSG.Quasithin.Chapter12.Section03

open BinarySevenCode

/-- The plane displayed in the proof of Lemma 12.3.9. -/
public def weightFourPlane : Submodule (ZMod 2) Word :=
  Submodule.span (ZMod 2) {![1, 1, 1, 1, 0, 0, 0], ![0, 0, 1, 1, 1, 1, 0]}

public theorem weightFourPlane_lt_simplexCode : weightFourPlane < simplexCode := by
  have hle : weightFourPlane ≤ simplexCode := by
    apply Submodule.span_le.mpr
    intro v hv
    rcases hv with rfl | hv
    · exact (mem_simplexCode_iff _).mpr ⟨![1, 0, 0], by decide⟩
    · rcases hv with rfl
      exact (mem_simplexCode_iff _).mpr ⟨![0, 1, 0], by decide⟩
  have hzero : weightFourPlane ≤ (LinearMap.proj 6 : Word →ₗ[ZMod 2] ZMod 2).ker := by
    apply Submodule.span_le.mpr
    intro v hv
    rcases hv with rfl | hv
    · rfl
    · rcases hv with rfl
      rfl
  apply lt_of_le_of_ne hle
  intro heq
  have hc : (![1, 0, 1, 0, 1, 0, 1] : Word) ∈ simplexCode :=
    (mem_simplexCode_iff _).mpr ⟨![0, 0, 1], by decide⟩
  rw [← heq] at hc
  have hz := hzero hc
  exact one_ne_zero (show (1 : ZMod 2) = 0 from hz)

/-- The source's proposed dimension-two bound fails even inside the actual
augmentation module. This does not refute its global group-theoretic lemma. -/
public theorem exists_rank_three_weight_four_subspace :
    ∃ U : Submodule (ZMod 2) Word, U ≤ evenWords ∧
      Module.finrank (ZMod 2) U = 3 ∧ ∀ v ∈ U, v ≠ 0 → weight v = 4 := by
  exact ⟨simplexCode, simplexCode_le_evenWords, finrank_simplexCode,
    fun _ hv hne => weight_of_mem_simplexCode hv hne⟩

end CFSG.Quasithin.Chapter12.Section03

module
public import Theory.Mathieu.M24.LocalGeometry.FourNormalizers.Overgroups.TrioCore
public import Theory.Mathieu.M24.LocalGeometry.OctadCharacteristicTwo
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Strict characteristic-two overgroups for the three M₂₄ four-normalizers

The full normalizers of the exact zero-based catalogue rows 1 and 2
preserve the octad fixed by Sylow element 106. The normalizer of row 3 preserves the
trio of fixed octads of its three nonidentity elements. The octad and trio
stabilizers have self-centralizing two-cores, hence F* = O₂. Explicit native
permutations belong to the respective stabilizers and fail to normalize
the four-groups, making each containment strict.

This supplies the three concrete inputs to `fourNormalizerOvergroups_of_rows`
in the unchanged `FourNormalizers.Reduction` module. No normalizer orders,
maximal-subgroup classification, or catalogue-wide normalizer claims are used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the sporadic
paragraph of 15.3.43, printed p.1140; GLS3, Table 5.3e.
-/

public section
namespace Sporadic.Mathieu.M24LocalGeometry.FourNormalizers
open Subgroup

private theorem row_overgroup (r : Fin 3) :
    ∃ D : Subgroup M24, normalizer (EvenCatalogue.ambient (rowNumber r) : Set M24) < D ∧
      Theory.GroupTheory.generalizedFitting D = pCore 2 D := by
  by_cases hr : r = 2
  · subst r
    refine ⟨trioGroup, lt_iff_le_not_ge.mpr ⟨normalizer_le_geometry 2, ?_⟩, ?_⟩
    · intro h
      exact witness_not_normalizer 2 (h trio_witness_mem)
    · exact Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
        trio_core_selfCentralizing
  · refine ⟨octadStabilizer commonOctad,
      lt_iff_le_not_ge.mpr ⟨normalizer_le_octad r hr, ?_⟩, ?_⟩
    · intro h
      have hn := witness_not_normalizer r
      rw [if_neg hr] at hn
      exact hn (h octad_witness_mem)
    · exact Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
        (LinearFourCore.octad_core_selfCentralizing commonOctad)

/-- Each of the three normal four-group rows has a strict overgroup with F* = O₂.
The indices are precisely the zero-based rows of `EvenCatalogue`. -/
theorem three_normalizer_overgroups (i : Fin 22) (hi : i = 1 ∨ i = 2 ∨ i = 3) :
    ∃ D : Subgroup M24, normalizer (EvenCatalogue.ambient i : Set M24) < D ∧
      Theory.GroupTheory.generalizedFitting D = pCore 2 D := by
  rcases hi with rfl | rfl | rfl
  · exact row_overgroup 0
  · exact row_overgroup 1
  · exact row_overgroup 2

end Sporadic.Mathieu.M24LocalGeometry.FourNormalizers

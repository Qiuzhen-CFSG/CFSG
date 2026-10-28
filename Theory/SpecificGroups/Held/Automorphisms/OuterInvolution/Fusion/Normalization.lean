module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion.Sylow
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion.Table

/-!
# The outer word normalizes the fixed Held Sylow

Conjugating each of the four original Sylow generators gives a specified
binary word in that subgroup. Both sides are already in the full Held
normalizer, so its certified four-point base suffices to check the identities.
Closure and finiteness then give normalization of the entire embedded subgroup.
Source: GLS3 Table 5.3p; the fixed ATLAS degree-2058 permutation model.
-/

namespace Held.OuterInvolution.Fusion
open Subgroup LocalPairs LocalPairs.SylowGeometry
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

private def imageIndex : Fin 4 → Fin 1024
  | 0 => 256
  | 1 => 3
  | 2 => 450
  | 3 => 698

private theorem generator_images : ∀ i : Fin 4, ∀ x : Fin 4,
    (outerPerm * generatorPerm i * outerPerm⁻¹) ⟨x.val, by omega⟩ =
      InvolutionFixedData.Coverage.normalPerm (imageIndex i) ⟨x.val, by omega⟩ := by
  decide +kernel

private theorem outer_conj_generator (i : Fin 4) :
    outer * innerEmbedding (Calculations.generator i) * outer⁻¹ =
      innerEmbedding (normalForm (imageIndex i)).val := by
  apply normalizer_ext_four
  intro x
  change (outer.val * representation (Calculations.generator i) * outer.val⁻¹)
    ⟨x.val, by omega⟩ = representation (normalForm (imageIndex i)).val ⟨x.val, by omega⟩
  rw [← outerPerm_eq, ← generatorPerm_eq, InvolutionFixedData.Coverage.normalForm_representation]
  exact generator_images i x

/-- The explicit outer involution lies in the full normalizer of the embedded inner Sylow. -/
public theorem outer_mem_fullSylow : outer ∈ fullSylow := by
  rw [fullSylow, mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rw [map_le_iff_le_comap, map_le_iff_le_comap, Calculations.representative, closure_le]
    rintro _ ⟨i, rfl⟩
    change outer * innerEmbedding (Calculations.generator i) * outer⁻¹ ∈
      Calculations.representative.map innerEmbedding
    rw [outer_conj_generator]
    exact mem_map_of_mem innerEmbedding (normalForm (imageIndex i)).property
  · exact (Nat.card_congr ((MulAut.conj outer).subgroupMap
      (Calculations.representative.map innerEmbedding)).toEquiv).le

end Held.OuterInvolution.Fusion

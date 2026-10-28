module

public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.CharacteristicNormalizerClosure

/-!
# Normalizer control from a unique maximal two-local overgroup

If `M` is the only maximal two-local containing `J`, every two-local containing
`J` lies in `M`. Apply this to normalizers of characteristic subgroups of a
two-group to control the full characteristic-normalizer closure.

These elementary finite-group arguments are used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March 2004),
§4.1, especially Lemmas 4.1.4(2) and 4.1.5(2), printed pp. 606–608.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial two-subgroup normalized by a uniqueness subgroup has its
whole normalizer in that subgroup's unique maximal two-local overgroup. -/
theorem normalizer_le_of_unique_maximalTwoLocal {J M V : Subgroup G}
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → J ≤ N → N = M)
    (hV : IsPGroup 2 V) (hne : V ≠ ⊥) (hJV : J ≤ normalizer (V : Set G)) :
    normalizer (V : Set G) ≤ M := by
  have hlocal : IsTwoLocal (normalizer (V : Set G)) := ⟨V, hne, hV, rfl⟩
  obtain ⟨N, hVN, hN⟩ := Finite.exists_le_maximal hlocal
  exact (hunique N hN (hJV.trans hVN)) ▸ hVN

/-- The same uniqueness hypothesis controls all characteristic-subgroup
normalizers, with characteristicness taken inside `R`. -/
theorem characteristicNormalizerClosure_le_of_unique_maximalTwoLocal
    {J M R : Subgroup G}
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → J ≤ N → N = M)
    (hR : IsPGroup 2 R) (hJR : J ≤ normalizer (R : Set G)) :
    R.characteristicNormalizerClosure ≤ M := by
  apply (characteristicNormalizerClosure_le_iff R M).mpr
  intro C hC hne
  let := hC
  apply normalizer_le_of_unique_maximalTwoLocal hunique
    ((hR.to_subgroup C).map R.subtype)
  · exact fun h => hne ((C.map_eq_bot_iff_of_injective R.subtype_injective).mp h)
  · exact hJR.trans (normalizer_le_normalizer_characteristic_image R C)

end Subgroup

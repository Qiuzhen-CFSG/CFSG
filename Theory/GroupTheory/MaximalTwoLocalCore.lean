module
public import Theory.GroupTheory.TwoLocalUniqueness
public import Theory.GroupTheory.CharacteristicNormalizerClosure
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The core and characteristic normalizers of a maximal two-local

A maximal two-local has a nontrivial two-core and equals its full normalizer.
Every nontrivial characteristic subgroup of that core is normalized by the
same maximal local, so its full normalizer also lies there. Consequently
the characteristic-normalizer closure of the core is exactly that local.

Source: Aschbacher–Smith A.4.4 and 14.1.14, printed pp.58,979.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem maximalTwoLocal_core_ne_bot {M : Subgroup G} (hM : IsMaximalTwoLocal M) :
    M.pCoreIn 2 ≠ ⊥ := by
  obtain ⟨Q,hQ,hp,hMQ⟩ := hM.1
  have hQM : Q ≤ M := hMQ ▸ Q.le_normalizer
  have hQc := le_pCoreIn_of_normalizes hp hQM hMQ.le
  exact fun he => hQ (bot_unique (he ▸ hQc))

theorem maximalTwoLocal_normalizer_core {M : Subgroup G} (hM : IsMaximalTwoLocal M) :
    normalizer (M.pCoreIn 2 : Set G) = M := by
  have hMN : M ≤ normalizer (M.pCoreIn 2 : Set G) := M.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  exact le_antisymm (hM.2 ⟨_,maximalTwoLocal_core_ne_bot hM,isPGroup_pCoreIn 2 M,rfl⟩ hMN) hMN

theorem maximalTwoLocal_characteristicNormalizer_core
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) :
    (M.pCoreIn 2).characteristicNormalizerClosure = M := by
  apply le_antisymm
  · apply (characteristicNormalizerClosure_le_iff _ _).mpr
    intro C hC hne
    let := hC
    have hn : M ≤ normalizer (C.map (M.pCoreIn 2).subtype : Set G) :=
      (maximalTwoLocal_normalizer_core hM).symm.le.trans
        (normalizer_le_normalizer_characteristic_image (M.pCoreIn 2) C)
    have hcn : C.map (M.pCoreIn 2).subtype ≠ ⊥ := fun he =>
      hne ((map_eq_bot_iff_of_injective _ (M.pCoreIn 2).subtype_injective).mp he)
    exact hM.2 ⟨_,hcn,((isPGroup_pCoreIn 2 M).to_subgroup C).map _,rfl⟩ hn
  · exact (maximalTwoLocal_normalizer_core hM).symm.le.trans
      (normalizer_le_characteristicNormalizerClosure_self _
        (maximalTwoLocal_core_ne_bot hM))
end Theory.GroupTheory

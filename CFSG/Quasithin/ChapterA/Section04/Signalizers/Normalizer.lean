module

public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Subnormal
public import Theory.GroupTheory.PCorePrimeToIndex
public import Mathlib.GroupTheory.Nilpotent

/-!
# Normalizers of maximal two-signalizers

Maximality recovers a signalizer as the two-core of its normalizer when
the relative normalizer index is odd. If the whole normalizer lies in M,
the normalizer condition in finite two-groups makes local maximality global.
Neither argument requires extra subnormality hypotheses.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.4.2(6), printed p. 57.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

/-- A.4.2(6), first assertion. The displayed index is
[N_G(R) : M ∩ N_G(R)], since `subgroupOf` restricts M to N_G(R). -/
theorem maximal_signalizer_eq_normalizer_core_of_odd_index (X M R : Subgroup G)
    (hR : IsMaximalTwoSignalizer X M R)
    (hodd : Odd (M.subgroupOf (normalizer (R : Set G))).index) :
    R = (normalizer (R : Set G)).pCoreIn 2 := by
  have hm := (isMaximalTwoSignalizer_iff X M R).mp hR
  have hRC : R ≤ (normalizer (R : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hm.1.isPGroup le_normalizer le_rfl
  have hCM : (normalizer (R : Set G)).pCoreIn 2 ≤ M := by
    have hc := (pCore_le_map_pCore_of_prime_not_dvd_index
      (M.subgroupOf (normalizer (R : Set G))) hodd.not_two_dvd_nat).trans (map_subtype_le _)
    rintro g ⟨n, hn, rfl⟩
    exact hc hn
  have hCN : X ≤ normalizer ((normalizer (R : Set G)).pCoreIn 2 : Set G) :=
    hm.1.normalizes.trans (le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact le_antisymm hRC (hm.2 _ ((isTwoSignalizer_iff _ _ _).mpr
    ⟨hCM, isPGroup_pCoreIn _ _, hCN⟩) hRC)

/-- A.4.2(6), second assertion: a contained normalizer makes local
maximality global. -/
theorem maximal_signalizer_in_top_of_normalizer_le (X M R : Subgroup G)
    (hR : IsMaximalTwoSignalizer X M R)
    (hNM : normalizer (R : Set G) ≤ M) :
    IsMaximalTwoSignalizer X ⊤ R := by
  have hm := (isMaximalTwoSignalizer_iff X M R).mp hR
  apply (isMaximalTwoSignalizer_iff X ⊤ R).mpr
  refine ⟨(isTwoSignalizer_iff _ _ _).mpr ⟨le_top, hm.1.isPGroup, hm.1.normalizes⟩, ?_⟩
  intro S hS hRS
  have hN : IsTwoSignalizer X M (S ⊓ normalizer (R : Set G)) := by
    apply (isTwoSignalizer_iff _ _ _).mpr
    exact ⟨inf_le_right.trans hNM, hS.isPGroup.to_le inf_le_left,
      (le_inf hS.normalizes (hm.1.normalizes.trans le_normalizer)).trans
        inf_normalizer_le_normalizer_inf⟩
  have he : S ⊓ normalizer (R : Set G) = R :=
    le_antisymm (hm.2 _ hN (le_inf hRS le_normalizer)) (le_inf hRS le_normalizer)
  let : Group.IsNilpotent S := hS.isPGroup.isNilpotent
  have hn : normalizer (R.subgroupOf S : Set S) = R.subgroupOf S := by
    rw [← subgroupOf_normalizer_eq hRS]
    ext x
    change (x : G) ∈ normalizer (R : Set G) ↔ (x : G) ∈ R
    constructor
    · intro hx
      exact he ▸ (show (x : G) ∈ S ⊓ normalizer (R : Set G) from ⟨x.property, hx⟩)
    · intro hx
      exact le_normalizer hx
  exact subgroupOf_eq_top.mp
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent _ hn)
end CFSG.Quasithin.ChapterA.Section04

end

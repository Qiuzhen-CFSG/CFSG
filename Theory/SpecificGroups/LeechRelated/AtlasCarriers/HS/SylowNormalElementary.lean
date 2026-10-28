module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Structure
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.LargeNormalizerThreePart

/-!
# Normal elementary subgroups of an HS Sylow

The intrinsic catalogue for the specified Sylow has three elementary entries,
each of order at most eight. Conjugating an arbitrary Sylow to that representative
bounds every elementary two-subgroup it normalizes; maximality first puts that
subgroup in the Sylow itself.

Source: GLS3 Table 5.3m, using the native HS normal-elementary catalogue.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.HS

/-- An elementary two-subgroup normalized by a full Sylow has order at most eight. -/
theorem normal_elementary_card_le_eight (S : Sylow 2 Carrier)
    (U : Subgroup Carrier) (hU : IsElementaryAbelian 2 U)
    (hS : (S : Subgroup Carrier) ≤ normalizer (U : Set Carrier)) : Nat.card U ≤ 8 := by
  let := hU
  have hUS : U ≤ S := by
    have hh := S.is_maximal' (S.isPGroup'.to_sup_of_normal_right'
      (IsElementaryAbelian.isPGroup 2 U) hS) le_sup_left
    exact sup_eq_left.mp hh
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier S BlockNormalizer.baseSylow
  let e := MulAut.conj g
  let V := U.map e.toMonoidHom
  have hV : V ≤ EvenLocalCandidates.subgroup := by
    have hh := map_mono (f := e.toMonoidHom) hUS
    change ((U.map e.toMonoidHom) : Subgroup Carrier) ≤ (g • S : Sylow 2 Carrier) at hh
    rw [hg] at hh
    exact hh
  have hN : EvenLocalCandidates.subgroup ≤ normalizer (V : Set Carrier) := by
    have hh := (map_mono (f := e.toMonoidHom) hS).trans (le_normalizer_map e.toMonoidHom)
    change ((g • S : Sylow 2 Carrier) : Subgroup Carrier) ≤ _ at hh
    rw [hg] at hh
    exact hh
  have hcard : Nat.card (V.subgroupOf EvenLocalCandidates.subgroup) = Nat.card U :=
    (Nat.card_congr (subgroupOfEquivOfLe hV).toEquiv).trans
      (card_map_of_injective e.injective)
  by_cases hzero : V.subgroupOf EvenLocalCandidates.subgroup = ⊥
  · rw [←hcard,hzero,card_bot]
    omega
  have hn := (normal_subgroupOf_iff_le_normalizer hV).mpr hN
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map e.toMonoidHom
  have he : IsElementaryAbelian 2 (V.subgroupOf EvenLocalCandidates.subgroup) :=
    IsElementaryAbelian.subgroupOf hV
  obtain ⟨i,hi⟩ := EvenLocalCandidates.normal_elementary_catalogue _ hzero hn he
  have hh := EvenLocalCandidates.elementary_card_le_eight i
  rw [←hi,card_map_of_injective EvenLocalCandidates.subgroup.subtype_injective,hcard] at hh
  exact hh

end Sporadic.LeechRelated.HS

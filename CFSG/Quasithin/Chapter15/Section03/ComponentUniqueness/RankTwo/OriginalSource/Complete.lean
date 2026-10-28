module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.OriginalSource.Models

/-!
# The minimal-outside shadow from the original rank-two argument

The ordinary component is chosen from the actual generalized Fitting subgroup.
Source37 and the independent source38 input build the containment premises;
39--41 construct the literal centralizer quotient. The marked source model
inspection then contradicts the rank-two alternative of11. Only its S₃-shadow
consequence is exported here, as required by the final Chapter E assembly.

The independent original characteristic-two exclusion13 and rank-two
containment38 remain explicit until their source producers are completed.
Source: Aschbacher--Smith, 15.3.35, printed pp.1135--1139.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.OriginalSource
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The rank-two branch on a minimal outside subgroup, using only the two
independently owned earlier source results. -/
theorem rank_two_false_of_earlier
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h13 : ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal)
    (h38 : ∀ L : Subgroup G, L ≤ I → IsComponent I (L.subgroupOf I) →
      primeRank 3 L = 2 → d.Yplus ≤ L)
    (htwo : OutsideStructure.RankTwoCase d I) : False := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI.1
  obtain ⟨K,hK⟩ := exists_ordinary_component_of_fstar_ne_twoCore h11.odd_core (h13 I hI.1)
  let L := K.map I.subtype
  have hLI : L ≤ I := map_subtype_le K
  have hrel : L.subgroupOf I = K := subgroupOf_map_subtype_eq K
  have hL : IsComponent I (L.subgroupOf I) := hrel.symm ▸ hK
  obtain ⟨z,hz,hzS,hcz,h⟩ := containment_inputs_from_selection hG d hempty hM hu hmany
    h13 hI.1 htwo hLI hL (h38 L hLI hL)
  obtain ⟨hn,c⟩ := component_setup_of_source_inputs d hM.1.1 h13 hI h
  let := hn
  exact no_component_of_original_models hG d hempty hM hu hmany h hz hzS hcz c

/-- The exact shadow consumed by the final uniqueness proof. -/
theorem source_lemma_15_3_35_shadow_of_earlier
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h13 : ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal)
    (h38 : OutsideStructure.RankTwoCase d I →
      ∀ L : Subgroup G, L ≤ I → IsComponent I (L.subgroupOf I) →
      primeRank 3 L = 2 → d.Yplus ≤ L) : SymmetricThreeShadow d.Yplus d.S := by
  rcases (OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI.1).local_structure with htwo | hone
  · exact (rank_two_false_of_earlier hG d hempty hM hu hmany h13 hI (h38 htwo) htwo).elim
  · exact hone.2.1

end CFSG.Quasithin.Chapter15.Section03.RankTwo.OriginalSource

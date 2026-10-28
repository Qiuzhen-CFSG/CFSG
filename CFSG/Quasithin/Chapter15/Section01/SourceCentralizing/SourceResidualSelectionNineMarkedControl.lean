module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialAmbient
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ResidualNormalizer

/-!
# Marked core control from the original maximal-overgroup pair

The pair of maximal two-locals supplies uniqueness above C_Mc(Z1)T by
the original Thompson-center escape. Once T normalizes that marked
centralizer, characteristic two and uniqueness control its two-core and
its residual. These deductions require neither global residual
centralization of the chosen fixed subgroup nor a selected component.

The Nine row supplies the required marked normalization separately, using
its four-element fixed subgroup and the central line in the partner.

Source: Aschbacher--Smith 15.1.13, 15.1.18(7), and 15.1.19(2),
printed pp.1090,1092--1093.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Original marked two-core control using the actual overgroup pair and
marked normalization, without the global fixed-subgroup residual premise. -/
theorem PreparedChosenModule.marked_core_normalizer_control_of_pair
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hp : PreparedChosenModule T M V)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hTn : (T : Subgroup G) ≤ normalizer (centralizer (Z1 : Set G) ⊓ Mc : Set G)) :
    ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc ∧
      centralizer (Z1 : Set G) ⊓
        normalizer ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2 : Set G) =
          centralizer (Z1 : Set G) ⊓ Mc := by
  let MZ := centralizer (Z1 : Set G) ⊓ Mc
  let Q := MZ.pCoreIn 2
  have huJ := (hp.marked_centralizer_uniqueness_of_maximal_overgroups_pair
    hG T hempty hM hmany hJ htwo hZ).2
  have hnQ : normalizer (MZ : Set G) ≤ normalizer (Q : Set G) :=
    normalizer_le_normalizer_characteristic_image MZ (pCore 2 MZ)
  have hMZQ : MZ ≤ normalizer (Q : Set G) := MZ.le_normalizer.trans hnQ
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      MZ ⊔ (T : Subgroup G) ≤ N → N = Mc := by
    intro N hN hJN
    exact Set.mem_singleton_iff.mp
      (huJ ▸ (show N ∈ maximalTwoLocalOvergroups (MZ ⊔ (T : Subgroup G)) from ⟨hN,hJN⟩))
  have hc : Q.characteristicNormalizerClosure ≤ Mc :=
    characteristicNormalizerClosure_le_of_unique_maximalTwoLocal huniq
      (isPGroup_pCoreIn 2 MZ) (sup_le hMZQ (hTn.trans hnQ))
  have hQne : Q ≠ ⊥ := CaseIMarkedSubgroup.core_nontrivial hZ hZne hM hu hp
  have hnMc : normalizer (Q : Set G) ≤ Mc :=
    (normalizer_le_characteristicNormalizerClosure_self Q hQne).trans hc
  exact ⟨hc,le_antisymm (inf_le_inf_left _ hnMc) (le_inf inf_le_left hMZQ)⟩

/-- Original marked residual-normalizer control from the pair and actual
Sylow restriction. The marked residual is nontrivial because the marked
centralizer escapes M by Thompson-center escape. -/
theorem PreparedChosenModule.marked_residual_normalizer_control_of_pair
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hp : PreparedChosenModule T M V)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hTn : (T : Subgroup G) ≤ normalizer (centralizer (Z1 : Set G) ⊓ Mc : Set G))
    (hSyl : ∃ P : Sylow 2 (centralizer (Z1 : Set G)),
      (P : Subgroup (centralizer (Z1 : Set G))).map (centralizer (Z1 : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer (Z1 : Set G)) :
    normalizer ((pResidual 2 (centralizer (Z1 : Set G) ⊓ Mc : Subgroup G)).map
      (centralizer (Z1 : Set G) ⊓ Mc).subtype : Set G) ≤ Mc := by
  let G1 := centralizer (Z1 : Set G)
  let MZ := G1 ⊓ Mc
  let Q := MZ.pCoreIn 2
  let J := MZ ⊔ (T : Subgroup G)
  let Y := (pResidual 2 MZ).map MZ.subtype
  obtain ⟨hescape,huJ⟩ := hp.marked_centralizer_uniqueness_of_maximal_overgroups_pair
    hG T hempty hM hmany hJ htwo hZ
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)).trans hMc.2
  have hJnorm : J ≤ normalizer (MZ : Set G) := sup_le MZ.le_normalizer hTn
  have hJQ : J ≤ normalizer (Q : Set G) :=
    hJnorm.trans (normalizer_le_normalizer_characteristic_image MZ (pCore 2 MZ))
  have hQJ : Q ≤ J := (pCoreIn_le 2 _).trans le_sup_left
  have hQne : Q ≠ ⊥ := CaseIMarkedSubgroup.core_nontrivial hZ hZne hM hu hp
  have hJHe : J ∈ Chapter1.He G := by
    apply Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T)
    refine ⟨?_,show (T : Subgroup G) ≤ J from le_sup_right⟩
    intro hb
    exact hQne (bot_unique ((le_pCoreIn_of_normalizes
      (isPGroup_pCoreIn 2 MZ) hQJ hJQ).trans_eq hb))
  have hYne : Y ≠ ⊥ := by
    intro hb
    have hr : pResidual 2 MZ = ⊥ :=
      ((pResidual 2 MZ).map_eq_bot_iff_of_injective MZ.subtype_injective).mp hb
    have htwoMZ : IsPGroup 2 MZ := (isPGroup_quotient_pResidual 2).of_equiv
      ((QuotientGroup.quotientMulEquivOfEq hr).trans QuotientGroup.quotientBot)
    obtain ⟨P,hP⟩ := hSyl
    have hPMZ : (P : Subgroup G1) ≤ MZ.subgroupOf G1 := by
      intro x hx
      have hm : (x : G) ∈ (T : Subgroup G) ⊓ G1 :=
        hP ▸ mem_map_of_mem G1.subtype hx
      exact ⟨hm.2,hTMc hm.1⟩
    have he : MZ.subgroupOf G1 = (P : Subgroup G1) := P.is_maximal' htwoMZ.comap_subtype hPMZ
    have hm := congrArg (Subgroup.map G1.subtype) he
    rw [map_subgroupOf_eq_of_le (show MZ ≤ G1 from inf_le_left),hP] at hm
    exact hescape (hm.le.trans (inf_le_left.trans hM.1.2))
  have hJY : J ≤ normalizer (Y : Set G) :=
    hJnorm.trans (normalizer_le_normalizer_characteristic_image MZ (pResidual 2 MZ))
  exact normalizer_le_of_characteristic_two_unique (Chapter1.mem_He_iff.mp hJHe)
    (fun N hN hJN => Set.mem_singleton_iff.mp
      (huJ ▸ (show N ∈ maximalTwoLocalOvergroups J from ⟨hN,hJN⟩)))
    ((map_subtype_le _).trans le_sup_left) hYne hJY

end CFSG.Quasithin.Chapter15.Section01

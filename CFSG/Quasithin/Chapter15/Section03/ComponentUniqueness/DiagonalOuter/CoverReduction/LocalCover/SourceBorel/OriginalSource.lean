module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.LocalSetup

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.SelectedSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Solvability
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OddRank.Intersection
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.RankTwoRank

/-!
# Earlier source data for the actual rank-two component

The original selected local hypotheses supply the outside-family facts,
solvability and actual matrix setup used by the Borel argument. The
uniform exclusion 15.3.13 remains explicit. The cubic quotient also
forces three-rank two, including the extraspecial order-twenty-seven case.
Source: Aschbacher--Smith 15.3.11--13, 15.3.33 and 15.3.38.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
open ChapterA.Section05To06 Candidates Candidates.LinearCore
variable {G : Type*} [Group G] [Finite G]

theorem source_borel_earlier_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h13 : ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J)
    {I : Subgroup G} (htwo : OutsideStructure.RankTwoCase d I) :
    SourceBorel.Earlier d := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany
  have hq := (ComponentIntersection.cubic_quotient_facts d.Yplus htwo.1).1
  refine {
    sylow := fun J hJ => (h11 J hJ).sylow
    odd := fun J hJ => (h11 J hJ).odd_core
    rank := fun J hJ => (OutsideStructure.outside_sqtk hG d hJ).stronglyQuasithin
      3 (by decide) (by decide)
    theta_eq := fun J hJ => (h11 J hJ).theta_eq.symm
    normalizer_eq := fun J hJ => (h11 J hJ).normalizer_eq
    intersection_characteristic_two := ?_
    exclusion := h13
    solvable := ?_
    quotient_exponent := (ComponentIntersection.cubic_quotient_facts d.Yplus htwo.1).2.1
    shadow := htwo.2.1
    local_core := htwo.2.2.2.2.1
    module_normalizer := (InitialSource.UniformControl.source_local_eq_normalizer
      hG d.T hM.1).symm }
  · intro J hJ
    rw [← inf_subgroupOf_right d.M J]
    let e := subgroupOfEquivOfLe (H := d.M ⊓ J) (show d.M ⊓ J ≤ J from inf_le_right)
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv, pCore_map_iso, (h11 J hJ).generalized_fitting]
  · exact solvable_yplus_join_of_threeGroup_quotient
      (d.T.isPGroup'.to_le (show d.S ≤ (d.T : Subgroup G) from inf_le_left))
      (RankTwo.planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice) hq

theorem matrix_source_setup_of_earlier
    (d : CharacteristicTwo.LocalData G) (earlier : SourceBorel.Earlier d)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    {I L : Subgroup G} (h : SourceBorel.Setup d I L) : MatrixImage.SourceSetup d I L := by
  have hnormal := rank_two_component_normal_in h.component_le h.component
    (earlier.odd I h.outside) (earlier.rank I h.outside) h.component_rank
  have hn : I ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.component_le).mp hnormal
  have hindex : (normalizer (L : Set G)).relIndex I ≤ 2 := by
    rw [relIndex_eq_one.mpr hn]
    decide
  have hθ := earlier.theta_eq I h.outside
  have hne : componentPart d.Yplus L ≠ ⊥ :=
    ComponentIntersection.intersectionResidual_ne_bot_of_local_facts h.outside hθ
      h.component_le hindex h.residual_rank (by rw [h.component_rank]; decide) (earlier.rank I h.outside)
  obtain ⟨P, hP⟩ := earlier.sylow I h.outside
  have hSM : d.S ≤ d.M := inf_le_left.trans d.sylow_le
  have hYI : d.Yplus ≤ I := le_sup_left.trans h.outside.1.2
  have hSY : d.S ≤ normalizer (d.Yplus : Set G) :=
    RankTwo.planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice
  have hMI : generalizedFitting (d.M ⊓ I : Subgroup G) =
      pCore 2 (d.M ⊓ I : Subgroup G) := by
    let eMI : d.M.subgroupOf I ≃* (d.M ⊓ I : Subgroup G) :=
      { toFun := fun x => ⟨x, x.property, x.val.property⟩
        invFun := fun x => ⟨⟨x, x.property.2⟩, x.property.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    have he := congrArg (Subgroup.map eMI.toMonoidHom)
      (earlier.intersection_characteristic_two I h.outside)
    simpa only [map_generalizedFitting_equiv, pCore_map_iso] using he
  have hY : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y) := by
    rcases h7 with ⟨_, ⟨e⟩, _⟩ | ⟨⟨e⟩, _⟩
    · apply IsPGroup.of_card (n := 2)
      rw [Nat.card_congr e.toEquiv]
      simp [ThreeAlternatives.ElementaryNine, Nat.card_eq_fintype_card]
    · exact IsPGroup.of_card ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
  refine {
    outside := h.outside
    sylow := ⟨P, hP⟩
    component_le := h.component_le
    component := h.component
    odd_core := earlier.odd I h.outside
    component_outside := h.outside_component earlier
    orbit_eq := le_antisymm (le_conjugateSpanBy L d.S)
      (conjugateSpanBy_le le_rfl ((le_sup_right.trans h.outside.1.2).trans hn))
    rank_component := h.component_rank
    rank_yplus := h.residual_rank
    rank_overgroup := earlier.rank I h.outside
    theta_eq := hθ
    normalizer_eq := earlier.normalizer_eq I h.outside
    quotient_three := hY
    yplus_quotient_three := IsPGroup.of_exponent_dvd_pow (n := 1)
      (by simpa only [pow_one] using earlier.quotient_exponent)
    intersection_characteristic_two := hMI
    residual_ne := hne
    core_normalizes := (pCoreIn_le 2 _).trans (h.outside.1.2.trans hn)
    component_cores_le := ComponentIntersection.cores_le_localCore h.component_le h.component.isCComponent
      P hP hYI hSY (hYI.trans hn)
    shadow := earlier.shadow
    characteristic_two_containment := ?_ }
  let := earlier.solvable
  intro D hD hDN hDF
  exact lemma_15_3_33_1 h.outside earlier.sylow earlier.exclusion earlier.odd
    (hD.trans h.component_le) hDN hDF

theorem source_matrix_setup_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h13 : ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J)
    {I L : Subgroup G} (h : SourceBorel.Setup d I L) : MatrixImage.SourceSetup d I L := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I h.outside
  have htwo := ComponentIntersection.rank_two_case_of_three_rank_two d I h11.local_structure h.residual_rank
  have earlier := source_borel_earlier_from_selection hG d hempty hM hu hmany h13 htwo
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have h7 := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne).2.2.2.2.2.2
  exact matrix_source_setup_of_earlier d earlier h7 h

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem rank_two_yplus_of_rank_two_case
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (h : OutsideStructure.RankTwoCase d I) : primeRank 3 d.Yplus = 2 :=
  OutsideStructure.rankTwoCase_three_rank hG d hI h

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover

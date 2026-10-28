module
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.QuotientLocal
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Solvability
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Definitions
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.SecondAction

/-!
# The original rank-two containment inputs

The selected local data and marked ordinary component theorem supply every
input to 15.3.39--41. The two independent earlier source results retained here
are the characteristic-two exclusion13 and the rank-two containment38.
The model alternatives37 and literal splitting12 are proved by their original
source producers; no universal classification callback is used.

Source: Aschbacher--Smith, 15.3.33--41, printed pp.1134--1138.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.OriginalSource
open ChapterA.Section05To06
open DiagonalOuter.CoverReduction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem quotient_alternatives_of_original (d : CharacteristicTwo.LocalData G)
    (h : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action) :
    RankOne.PlaneGeometry.SourceQuotientAlternatives d.Y d.V := by
  rcases OutsideStructure.earlier_three_alternatives_of_source d h with h | ⟨h, _, _⟩
  · obtain ⟨e⟩ := h.quotient_equiv
    let : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) := {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := by
        apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        intro x
        apply Multiplicative.toAdd.injective
        change 3 • x.toAdd = 0
        funext i
        exact (by decide : ∀ a : ZMod 3, 3 • a = 0) _ }
    refine Or.inl ⟨IsElementaryAbelian.of_injective e.toMonoidHom e.injective, ?_⟩
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  · refine Or.inr ⟨h.extraspecial, h.quotient_card, ?_⟩
    have hc := congrArg (fun K : Subgroup G => K.subgroupOf d.Y) h.centralizer_eq
    rw [inf_subgroupOf_left, FusionCore.CosetSetup.ExtraspecialLocal.twoCenter,
      subgroupOf_map_subtype_eq] at hc
    rw [hc, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

/-- Every earlier containment premise on the original chosen component. -/
theorem containment_inputs_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h13 : ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J)
    {I L : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (h38 : primeRank 3 L = 2 → d.Yplus ≤ L) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ d.S ∧ centralizer ({z} : Set G) = d.Mc ∧
      ContainmentSourceInputs d I L z := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany
  have h11I := h11 I hI
  have earlier := LocalCover.source_borel_earlier_from_selection hG d hempty hM hu hmany h13 htwo
  obtain ⟨z,hz,hzS,hcz,h33⟩ :=
    Candidates.ComponentStructure.ordinary_component_structure_from_selection
      hG d hempty hM hu hmany hI hL
  obtain ⟨hne,_,hmax⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  obtain ⟨himage,_,_,_,_,hcore,hquot⟩ :=
    source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  have h9 := source_lemma_15_3_9_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  have hMc : d.Mc ∈ maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) :=
    hu ▸ Set.mem_singleton d.Mc
  have hTMc : (d.T : Subgroup G) ≤ d.Mc :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow d.T)).trans hMc.2
  obtain ⟨N,hN,horder⟩ :=
    InitialSource.UniformControl.source_exists_ordering_maximal_above hG d.T ⟨hMc.1,hTMc⟩
  rw [hmax N hN] at horder
  have hC : d.Mc = centralizer (d.Z : Set G) :=
    centralizer_eq_Mc_of_residual_dichotomy d.T d.M d.Mc d.sylow_le
      ⟨hMc.1,hTMc⟩ hne hMc.2 horder
      ((source_lemma_15_3_2_4 d.T d.action hM (le_inf d.sylow_le hTMc)
        inf_le_left).imp id And.right)
  have hQ := OutsideStructure.outside_twoCoreQuotient_sqtk hG d hI
  have hcomp := Chapter1.Section02.proposition_1_2_1_three_index_knownSimple hQ hL.isCComponent
  have horbit : (normalizer (L : Set G)).relIndex I ≤ 2 := by
    change ((normalizer (L : Set G)).subgroupOf I).index ≤ 2
    rw [subgroupOf_normalizer_eq hLI]
    rcases hcomp with hn | ⟨hn,_⟩
    · let := hn
      rw [normalizer_eq_top,index_top]
      decide
    · exact hn.le
  have hY : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus) :=
    IsPGroup.of_exponent_dvd_pow (n := 1)
      (by simpa only [pow_one] using earlier.quotient_exponent)
  have hr := (Candidates.SuzukiExclusion.lemma_15_3_34 hI earlier.sylow h13 earlier.odd
    (inf_le_left.trans d.sylow_le) h11I.normalizer_eq hY h11I.theta_eq hLI hL h33 horbit).2
  have hYrank := LocalCover.rank_two_yplus_of_rank_two_case hG d hI htwo
  refine ⟨z,hz,hzS,hcz,{
    outside := hI
    characteristic_two := hG.evenCharacteristic d.T d.M hM.1.1 d.sylow_le
    centralizer_overgroup := hC
    residual_image := himage
    residual_core := hcore
    residual_quotient := quotient_alternatives_of_original d hquot
    not_alternating_square := h9.2
    outside_structure := h11I
    rank_two_case := htwo
    component_le := hLI
    component := hL
    component_structure := h33
    strongly_quasithin := (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin
    component_rank_pos := hr
    residual_rank := hYrank
    component_alternative := hcomp
    invariant_subgroup := ?_
    alternatives := Candidates.RankTwoSource.source_lemma_15_3_37_from_selection
      hG d hempty hM hu hmany h13 hI htwo hI hLI hL
    rank_two_containment := h38
    intersection_splitting := ?_ }⟩
  · intro D hD hDN hDF
    have hspan : localSpan L d.S ≤ I :=
      conjugateSpanBy_le hLI ((le_sup_right.trans hI.1.2).trans I.le_normalizer)
    exact lemma_15_3_33_1_of_threeGroup_quotient hI earlier.sylow h13 earlier.odd
      (inf_le_left.trans d.sylow_le) h11I.normalizer_eq hY (hD.trans hspan) hDN hDF
  · intro hLrank hinner
    obtain ⟨hp,_,_,_,hq,hpart,_⟩ :=
      ComponentIntersection.source_lemma_15_3_12_2_three_parts_from_selection
        hG d hempty hM hu hmany hI hLI hL.isCComponent hYrank hLrank hinner
    exact ⟨hp,hpart,hq⟩

/-- Source39--41 construct the actual component setup in I/C_I(L). -/
theorem component_setup_of_source_inputs
    (d : CharacteristicTwo.LocalData G) (hM : IsMaximalTwoLocal d.M)
    (h13 : ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J)
    {I L : Subgroup G} {z : G} (hI : I ∈ d.HplusMinimal)
    (h : ContainmentSourceInputs d I L z) :
    ∃ hn : (L.subgroupOf I).Normal,
      @NonCharacteristicTwo.ComponentSetup G _ I L d.M d.Yplus d.S hn := by
  have hYL := source_lemma_15_3_40 d h
  have horbit := source_lemma_15_3_39 d h
  have hSL : d.S ≤ normalizer (L : Set G) := by
    rw [horbit]
    exact le_normalizer_componentOrbit L d.S
  obtain ⟨P,hP⟩ := h.outside_structure.sylow
  have hout : ¬ L ≤ d.M := by
    simpa only [map_subgroupOf_eq_of_le h.component_le] using h.component_structure.outside
  have hgen := eq_component_join_of_minimal hI P hP hYL h.component_le hout
  let hn : (L.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer
    (hgen ▸ sup_le L.le_normalizer hSL)
  let := hn
  let := h.component.2
  let eL := subgroupOfEquivOfLe h.component_le
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv eL
  have ho : pPrimeCore 2 L = ⊥ := by
    rw [← pPrimeCore_map_iso 2 eL,h.component_structure.odd_core,Subgroup.map_bot]
  obtain ⟨hsimple,hfitting,_,hlocal⟩ := lemma_15_3_41_of_earlier d hM h.outside
    h.component_le hgen h.component h.component_structure P hP hYL
    h.outside_structure.normalizer_eq h.outside_structure.generalized_fitting
    h.rank_two_case.2.1 h13
  exact ⟨hn,{
    component_le := h.component_le
    component_quasisimple := inferInstance
    join_eq := hgen
    yplus_le := hYL
    outside := hout
    sylow_le_M := inf_le_left.trans d.sylow_le
    minimal := hI
    sylow := ⟨P,hP⟩
    oddCore := ho
    center_eq := IsQuasisimple.center_eq_pCore ho
    normalizer_eq := h.outside_structure.normalizer_eq
    theta_eq := h.outside_structure.theta_eq.symm
    intersection_fitting := h.outside_structure.generalized_fitting
    yplus_twoResidual := OutsideStructure.chosen_residual_eq d.M d.Mc d.S d.V₁ d.Yplus d.choice
    yplus_three_rank := h.residual_rank
    yplus_exponent := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (ComponentIntersection.cubic_quotient_facts d.Yplus h.rank_two_case.1).2.1
    shadow := h.rank_two_case.2.1
    simple_image := hsimple
    fitting_eq := hfitting
    quotient_local := hlocal }⟩

/-- The natural action and source36 core identity give every ambient module
premise used in the final model inspection. -/
theorem action_setup_of_source_inputs
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G} {z : G}
    (h : ContainmentSourceInputs d I L z) :
    NonCharacteristicTwo.ActionSetup d.M d.Y d.S d.V d.V₁ d.V₂ d.Yplus := by
  let : IsElementaryAbelian 2 d.V := d.action.elementary_of_le le_rfl
  have hVR : d.V ≤ d.R := by
    rw [h.rank_two_case.2.2.2.2.1]
    refine le_inf ((OutsideStructure.LocalBranches.v_le_s d).trans inf_le_left) ?_
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hy⟩ : d.V) ⟨x,hx⟩)
  have hRC : d.R ≤ centralizer (d.V : Set G) := by
    rw [h.rank_two_case.2.2.2.2.1]
    exact inf_le_right
  exact {
    hypothesis := d.choice
    elementary := inferInstance
    card := d.action.card_vector
    moved := d.action.commutator_eq_of_residual_image d.Y
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) h.residual_image
    le_sylow := OutsideStructure.LocalBranches.v_le_s d
    first_le := d.action.plane_le _
    second_le := d.action.plane_le _
    first_card := d.action.card_plane _
    second_card := d.action.card_plane _
    plane_join := natural_planes_sup d.action (by decide)
    plane_disjoint := (natural_planes_disjoint d.action (by decide)).eq_bot
    normalized := d.action.normalizes
    central_radical := by
      intro x hx
      refine ⟨⟨x,hVR hx⟩,mem_center_iff.mpr (fun r => ?_),rfl⟩
      exact Subtype.ext (hRC r.property x hx).symm
    caseTwo_moved := fun hc =>
      (OutsideStructure.LocalBranches.second_choice_commutator d hc h.residual_image).1
    normalizer_control := fun hc => (h.outside_structure.second_choice hc).2.1 }

end CFSG.Quasithin.Chapter15.Section03.RankTwo.OriginalSource

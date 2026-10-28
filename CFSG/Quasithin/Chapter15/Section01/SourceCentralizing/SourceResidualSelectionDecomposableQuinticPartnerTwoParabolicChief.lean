module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Residual.CoreReduction
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ChosenSourceInputs
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceMovement

/-!
# Two noncentral chiefs for the actual outside minimal parabolic

The actual minimal-parabolic hypothesis supplies unique Sylow-maximality
directly. Together with the original chosen-normalizer uniqueness it gives
a QRC configuration, without H-star membership or any identification of
the parabolic's maximal subgroup with its intersection with M.

The original ratio-two action is not dual FF. A unique noncentral chief
would therefore give a genuine noncentral reduced residual module, contrary
to source ordering for this same outside parabolic. The SQTK equality
theorem then gives exactly two noncentral chiefs on the same V-span.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open NoncentralChiefRefinement
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Direct QRC construction from the actual outside minimal parabolic.
Its unique maximal subgroup remains the one supplied by the parabolic. -/
theorem PreparedChosenModule.outside_minimalParabolic_qrc
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V P : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T:Subgroup G)≤centralizer (localModule T M:Set G))
    (h : PreparedChosenModule T M V)
    (hP : P∈Chapter1.HOver G (T:Set G))
    (hp : ChapterB.IsMinimalParabolicOver T P) (hout : ¬P≤M) :
    QRCConfiguration (chosenNormalizer T M V) P (T:Subgroup G) V := by
  let := h.elementary
  let N := chosenNormalizer T M V
  have hTN : (T:Subgroup G)≤N := sylow_le_chosenNormalizer T hM.1.2 h.normalized
  have huniq := source_chosenNormalizer_unique hG T hempty hM hJ
    h.nontrivial h.normalized h.seed_span
  have hcommon := Chapter3.no_common_normal_of_unique_maximal
    (isPGroup_pCoreIn 2 N) huniq hout
  obtain ⟨B,hTB,hBP⟩ := hp.1.2.exists
  have hi := (ChapterB.intrinsic_minimalParabolic T P B hp hTB hBP).1
  obtain ⟨Y,hY,hYu⟩ := (ChapterB.isMinimalParabolicOver_top_iff (T.subtype hP.2)).mp hi |>.1
  refine ⟨inferInstance,inferInstance,⟨T.subtype hTN,?_⟩,⟨T.subtype hP.2,?_⟩,
    module_le_chosenNormalizer T hM.1.2 h.le_selected h.normalized,
    inf_le_left.trans h.normalized,h.elementary,
    chosenNormalizer_actionImage_reduced T hM.1.2 h.le_selected h.normalized h.seed_span,
    ?_,chosenNormalizer_twoCore T hM.1.2 h.le_selected h.normalized h.seed_span,?_⟩
  · exact map_subgroupOf_eq_of_le hTN
  · exact map_subgroupOf_eq_of_le hP.2
  · refine ⟨Y,⟨hY.1,?_⟩,?_⟩
    · rw [←map_subgroupOf_eq_of_le hP.2]
      exact map_mono hY.2
    · intro Z hZ
      apply hYu Z
      refine ⟨hZ.1,?_⟩
      apply (map_le_map_iff_of_injective P.subtype_injective).mp
      change ((T:Subgroup G).subgroupOf P).map P.subtype≤Z.map P.subtype
      rw [map_subgroupOf_eq_of_le hP.2]
      exact hZ.2
  · intro K hKN hnK
    by_contra hK
    apply hcommon
    refine ⟨K,hKN,hK,Chapter3.normalIn_iff_le_normalizer.mpr ⟨?_,?_⟩⟩
    · exact hKN.trans ((pCoreIn_le 2 N).trans Chapter3.le_generated_left)
    · rwa [Chapter3.generated_eq_sup]

/-- The actual outside minimal parabolic has exactly two noncentral chief
factors on the span of the original module when that module is in its core. -/
theorem PreparedChosenModule.outside_minimalParabolic_two_chiefs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V P : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T:Subgroup G)≤centralizer (localModule T M:Set G))
    (h : PreparedChosenModule T M V)
    (hP : P∈Chapter1.HOver G (T:Set G))
    (hp : ChapterB.IsMinimalParabolicOver T P) (hout : ¬P≤M)
    (hVP : V≤P.pCoreIn 2) :
    IsElementaryAbelian 2 (conjugateSpan P V) ∧
      ∀ s : SeriesOn ((conjugateSpan P V).subgroupOf P), s.noncentralCount=2 := by
  let d := h.outside_minimalParabolic_qrc hG T hempty hM hJ hP hp hout
  let := h.elementary
  have hq : quadraticRatio (imageRepresentation (chosenNormalizer T M V) V d.module_normalized)=2 :=
    (chosenNormalizer_quadraticRatio_eq T hM.1.2 h.normalized).trans h.quadratic_ratio
  have hn := source_notFF_of_ratio_two d hq
  let he := source_elementary_span_of_notFF d hVP hn
  let := he
  let U := (conjugateSpan P V).subgroupOf P
  have hUP : conjugateSpan P V≤P := (span_le_right_core d hVP).trans (twoCore_le P)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUP
  have hsol : Group.IsSolvable (internalActionImage (chosenNormalizer T M V) V d.module_normalized) := by
    rw [show internalActionImage (chosenNormalizer T M V) V d.module_normalized=
      internalActionImage M V h.normalized from chosenNormalizer_actionImage_eq T hM.1.2 h.normalized]
    exact source_chosen_action_isSolvable hG T hempty hM V h.normalized h.le_local
  have hdual : ¬DualFF d := by
    intro hd
    have hf := ChapterB.SolvableDualFF.isFFModule_of_dual
      (imageRepresentation (chosenNormalizer T M V) V d.module_normalized) hsol
      d.module_reduced (imageRepresentation_injective _ _ _) hd
    have hh := (isFFModule_iff_quadraticRatio_le_one _).mp hf
    rw [hq] at hh
    norm_num at hh
  refine ⟨he,?_⟩
  intro s
  have hz := noncentralCount_ne_zero d h.nontrivial hVP s
  have ho : s.noncentralCount≠1 := by
    intro hc
    have huf : HasUniqueNoncentralChiefFactor P V := ⟨s,hc⟩
    rcases source_dualFF_or_coreClosure_centralizes d hVP huf with hd | hc
    · exact hdual hd
    · let I := ⁅conjugateSpan P V,(pResidual 2 P).map P.subtype⁆
      have hIP : I≤P := (residual_module_le_span d).trans hUP
      have hred := source_residual_module_reduced d hVP huf hc
      have hmov := source_thompson_moves_residual_module d hVP huf hc
      have hcent : centralizer (I.subgroupOf P:Set P)≠⊤ := by
        intro ht
        apply hmov
        intro j hj i hi
        have hJR : elementaryAbelianMaxJ (twoCoreIn (chosenNormalizer T M V))≤
            twoCoreIn (chosenNormalizer T M V) := sSup_le fun _ hA=>hA.1
        have hjP : j∈P := hP.2 (left_core_le_sylow d (hJR hj))
        have hh : (⟨j,hjP⟩:P)∈centralizer (I.subgroupOf P:Set P) := ht ▸ mem_top _
        exact congrArg P.subtype (hh ⟨i,hIP hi⟩ hi)
      exact hout (source_noncentral_reduced_minimalParabolic_le
        hG T hempty hM hJ hP hp (I.subgroupOf P) hred hcent)
  let S := T.subtype hP.2
  have hS : (S:Subgroup P).map P.subtype=(T:Subgroup G) := map_subgroupOf_eq_of_le hP.2
  obtain ⟨A,hA,hAQ,hquad⟩ := source_quadratic_max_actor d h.nontrivial hVP hn S hS
  have hnc : ¬A≤centralizer (U:Set P) := by
    intro ha
    exact hAQ ((le_inf hA.1 ha).trans
      (source_span_centralizer_sylow_le_core d h.nontrivial hVP hn S hS))
  exact (source_sqtk_multiple_equalities d h.nontrivial hVP
    (Chapter3.sqtk_of_mem_H hG hP.1) hq S hS s (by omega) A hA hquad hnc).1

/-- In the contained central-seed-core branch, the actual moving parabolic
selected by residual escape has the two-chief conclusion. Its original
proper-overgroup bound is preserved, without replacing its maximal subgroup. -/
theorem PreparedChosenModule.thompsonFixed_moving_parabolic_two_chiefs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T:Subgroup G)≤centralizer (localModule T M:Set G))
    (h : PreparedChosenModule T M V)
    (hVC : V≤(centralizer (centralInvolutions T:Set G)).pCoreIn 2)
    (hnot : ¬(pResidual 2 (centralizer (centralInvolutions T:Set G))).map
      (centralizer (centralInvolutions T:Set G)).subtype≤
        centralizer (thompsonFixed T V:Set G)) :
    let C := centralizer (centralInvolutions T:Set G)
    let K := (M⊓C)⊔((pResidual 2 C).map C.subtype⊓centralizer (thompsonFixed T V:Set G))
    ∃ P : Subgroup G, P≤C ∧ P∈Chapter1.HOver G (T:Set G) ∧
      ChapterB.IsMinimalParabolicOver T P ∧ IsSQTK KnownSimple.IsKnownSimple P ∧
      generalizedFitting P=pCore 2 P ∧ ¬P≤M ∧
      ¬(pResidual 2 P).map P.subtype≤centralizer (thompsonFixed T V:Set G) ∧
      (∀ Y : Subgroup G, (T:Subgroup G)≤Y → Y<P → Y≤K) ∧
      V≤P.pCoreIn 2 ∧ IsElementaryAbelian 2 (conjugateSpan P V) ∧
      ∀ s : SeriesOn ((conjugateSpan P V).subgroupOf P), s.noncentralCount=2 := by
  let C := centralizer (centralInvolutions T:Set G)
  obtain ⟨P,hPC,hP,hp,hSQ,hF,hout,hmove,hproper⟩ :=
    h.thompsonFixed_moving_minimalParabolic hG T hM hJ hnot
  have hTC : (T:Subgroup G)≤C := by
    intro t ht z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  have hQT : C.pCoreIn 2≤(T:Subgroup G) := by
    have hh := pCoreIn_le_sylow C (T.subtype hTC)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTC] at hh
  have hCQ : C≤normalizer (C.pCoreIn 2:Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hQP : C.pCoreIn 2≤P.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 C) (hQT.trans hP.2) (hPC.trans hCQ)
  have hVP : V≤P.pCoreIn 2 := hVC.trans hQP
  have hchief := h.outside_minimalParabolic_two_chiefs hG T hempty hM hJ hP hp hout hVP
  exact ⟨P,hPC,hP,hp,hSQ,hF,hout,hmove,hproper,hVP,hchief⟩

end CFSG.Quasithin.Chapter15.Section01

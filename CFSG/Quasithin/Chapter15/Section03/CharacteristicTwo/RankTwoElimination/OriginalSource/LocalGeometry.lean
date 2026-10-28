module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.SelectedSource
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.Commutator
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.Components
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.RankTwoRank

/-!
# Original rank-two local geometry

The original outside subgroup I and M intersect I satisfy the literal C.2.3
setup. Restriction to LR permits C.2.7's proved kernel and offender theorems.
Its Thompson normalizer control gives L = [L,J(R)], and V contained in Z(R)
puts the actual span of V in an elementary omega-center. The surviving
quasisimple component then makes this span two-reduced in LR.

These statements establish the geometric clauses of 15.3.16. They do not
assume or assert C.2.7's separate marked model classification. The rank-two
alternative propagates to every outside subgroup using the original 15.3.11.

Source: Aschbacher–Smith 15.3.13–16, printed pp.1125–1126.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open Chapter1.RadicalExclusions
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem localSpan_eq_map_normalClosure {A H : Subgroup G} (hAH : A ≤ H) :
    localSpan A H = (normalClosure (A.subgroupOf H : Set H)).map H.subtype := by
  let N := normalClosure (A.subgroupOf H : Set H)
  apply le_antisymm
  · apply conjugateSpanBy_le
    · intro a ha
      exact ⟨⟨a, hAH ha⟩, le_normalClosure ha, rfl⟩
    · exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le N)).mp (by
        rw [show (N.map H.subtype).subgroupOf H = N from
          comap_map_eq_self_of_injective H.subtype_injective N]
        infer_instance)
  · let : ((localSpan A H).subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy A H)
    have hh : normalClosure (A.subgroupOf H : Set H) ≤ (localSpan A H).subgroupOf H :=
      normalClosure_le_normal (comap_mono (le_conjugateSpanBy A H))
    rintro x ⟨y,hy,rfl⟩
    exact hh hy

/-- The actual C.2.3 configuration in I, with overgroup M∩I, from 15.3.11(5i). -/
theorem rankTwo_pushingUpSetup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (htwo : OutsideStructure.RankTwoCase d I) :
    PushingUpSetup KnownSimple.IsKnownSimple I d.R (d.MI I) := by
  have hRI : d.R ≤ I := (d.Yplus ⊔ d.S).pCoreIn_le 2 |>.trans hI.1.2
  have hRT : d.R ≤ (d.T : Subgroup G) := htwo.2.2.2.2.1.le.trans inf_le_left
  have hRMI : d.R ≤ d.MI I := le_inf (hRT.trans d.sylow_le) hRI
  have hRne : d.R ≠ ⊥ := by
    intro hb
    have hp : d.action.plane 1 = ⊥ := le_bot_iff.mp
      (((d.action.plane_le 1).trans (V_le_R d htwo.2.2.2.2.1)).trans hb.le)
    have hc := d.action.card_plane 1
    simp [hp] at hc
  refine ⟨OutsideStructure.outside_sqtk hG d hI,hRI,inf_le_right,?_,?_,?_⟩
  · refine ⟨?_,?_⟩
    · intro hb
      apply hRne
      simpa only [map_subgroupOf_eq_of_le hRI, Subgroup.map_bot] using
        congrArg (map I.subtype) hb
    · apply map_injective I.subtype_injective
      change ((normalizer (d.R.subgroupOf I : Set I)).pCoreIn 2).map I.subtype = _
      rw [map_pCoreIn_of_injective 2 _ I.subtype I.subtype_injective,
        ←subgroupOf_normalizer_eq hRI,subgroupOf_map_subtype]
      simpa only [inf_comm,map_subgroupOf_eq_of_le hRI] using htwo.2.2.2.2.2.1.symm
  · have hc := characteristicNormalizerClosure_subgroupOf_le hRI htwo.2.2.2.2.2.2.2
    exact fun x hx => ⟨hc hx,x.property⟩
  · rw [←localSpan_eq_map_normalClosure hRMI]
    exact htwo.2.2.2.2.2.2.1

/-- A selected relative C-component inherits the characteristic-two hypothesis. -/
theorem component_characteristicTwo (d : LocalData G) {I : Subgroup G}
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I) :
    generalizedFitting c.L = pCore 2 c.L := by
  have hcomp := LocalData.thompson_component_in c.le_thompson c.component
  have hF : generalizedFitting (c.L.subgroupOf I) = pCore 2 (c.L.subgroupOf I) := by
    apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    apply subnormal_core_selfCentralizing _ _ hcomp.subnormal
    rw [←hf]
    exact centralizer_generalizedFitting_le I
  have hm := congrArg (map (subgroupOfEquivOfLe (component_le c)).toMonoidHom) hF
  simpa only [map_generalizedFitting_equiv,pCore_map_iso] using hm

/-- The source C.2.7 input retains the original I and M∩I. The rank premise is
the literal hypothesis of 15.3.13, and normalization is supplied by 15.3.12(1). -/
theorem rankTwo_component_input
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus)
    (htwo : OutsideStructure.RankTwoCase d I) (hrank : primeRank 3 d.Yplus = 2)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I) :
    Input KnownSimple.IsKnownSimple I d.R (d.MI I) c.L := by
  have hc := LocalData.thompson_component_in c.le_thompson c.component
  have h12 := ComponentIntersection.source_lemma_15_3_12_1_from_selection
    hG d hempty hM hu hmany hI (component_le c) hc hrank c.rank_pos
  exact ⟨rankTwo_pushingUpSetup hG d hI htwo,⟨component_le c,hc⟩,
    c.core_quotient_quasisimple,component_characteristicTwo d hf c,
    fun h => c.outside (h.trans inf_le_left),h12.2.1⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]

/-- The literal Thompson-generation assertion in 15.3.16 follows from
C.2.7's proved normalizer control, without a block-classification premise. -/
theorem component_eq_commutator_thompson
    {κ : GroupClass} {I L R M : Subgroup G} (h : Input κ I R M L) :
    L = ⁅L,elementaryAbelianMaxJ R⁆ := by
  let J := L ⊔ R
  let LJ := L.subgroupOf J
  let A := elementaryAbelianMaxJ R
  let AJ := A.subgroupOf J
  let q := QuotientGroup.mk' (starKernel L R)
  let : LJ.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  have hAJ : A ≤ J := (sSup_le fun _ hA => hA.1).trans le_sup_right
  have hcomp : LJ.IsCComponent := h.component.2.subgroupOf_of_le le_sup_left h.join_le
  have hAN : AJ ≤ normalizer (LJ : Set J) := by
    rw [←subgroupOf_normalizer_eq (show L ≤ J from le_sup_left)]
    exact comap_mono ((sSup_le fun _ hA => hA.1).trans h.normalizes)
  have hfit := star_fitting_quasisimple (source_join_input h)
  have hcontrol := star_thompson_intersection_from_source h
  have hne : ⁅LJ.map q,AJ.map q⁆ ≠ ⊥ := by
    intro he
    have hn : starImage L R L ≤ normalizer (starImage L R A : Set (StarQuotient L R)) :=
      (commutator_eq_bot_iff_le_centralizer.mp he).trans (Subgroup.centralizer_le_normalizer _)
    exact (not_le_of_gt hcontrol.2) (fun x hx => hcontrol.1 ⟨hx,hn hx⟩)
  have he := cComponent_eq_commutator_of_image hcomp hAN q
    (QuotientGroup.mk'_surjective _) hfit.2 hne
  have hm := congrArg (map J.subtype) he
  simpa only [LJ,AJ,A,map_commutator,map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left),
    map_subgroupOf_eq_of_le hAJ] using hm

/-- Radical saturation is valid after restricting to LR, even though L is
only subnormal in the original I. -/
theorem component_joinCore_le_radical
    {κ : GroupClass} {I L R M : Subgroup G} (h : Input κ I R M L) :
    (L ⊔ R).pCoreIn 2 ≤ R := by
  let : (L.subgroupOf (L ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  exact source_joinCore_le_radical (source_join_input h)

/-- The actual seed V lies in the C.2.7 omega-center, using V≤Z(R)
and the characteristic-two self-centralizer of O₂(LR). -/
theorem component_seed_le_starV (d : LocalData G) {I L : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple I d.R (d.MI I) L)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    d.V ≤ (starV L d.R).map (L ⊔ d.R : Subgroup G).subtype := by
  let J := L ⊔ d.R
  let W := (starV L d.R).map J.subtype
  let : IsElementaryAbelian 2 d.V := d.action.elementary
  have hQR : J.pCoreIn 2 ≤ d.R := component_joinCore_le_radical h
  have hc : centralizer (pCore 2 L : Set L) ≤ pCore 2 L := by
    rw [←h.fitting]
    exact centralizer_generalizedFitting_le L
  have hJc := centralizer_pCore_sup_le 2 L d.R hc (isPGroup_pCoreIn 2 _) h.normalizes
  have hVW : d.V ≤ W := by
    intro v hv
    let vJ : J := ⟨v,mem_sup_right (V_le_R d hR hv)⟩
    have hvC : vJ ∈ centralizer (pCore 2 J : Set J) := by
      intro x hx
      exact Subtype.ext ((V_le_center_R d hR hv).2 x (hQR (mem_map_of_mem J.subtype hx)))
    refine ⟨vJ,?_,rfl⟩
    change vJ ∈ omegaOneCenterAmbient (pCore 2 J)
    exact (mem_omegaOneCenterAmbient_iff _ vJ).mpr
      ⟨hJc hvC,Subtype.ext (elemPow_eq_one_of_isElementaryAbelian v hv),
        fun x hx => hvC x hx⟩
  exact hVW

/-- V≤Z(R) puts the actual span of V under L inside the elementary
omega-center of O₂(LR). This proves the source's elementarity assertion
without replacing its span by the C.2.7 module. -/
theorem component_span_elementary (d : LocalData G) {I L : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple I d.R (d.MI I) L)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    IsElementaryAbelian 2 (d.componentSpan L) := by
  let J := L ⊔ d.R
  let W := (starV L d.R).map J.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map J.subtype
  have hVW : d.V ≤ W := component_seed_le_starV d h hR
  have hJW : J ≤ normalizer (W : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le (starV L d.R))).mp (by
      rw [show W.subgroupOf J = starV L d.R from
        comap_map_eq_self_of_injective J.subtype_injective _]
      infer_instance)
  exact IsElementaryAbelian.of_injective
    (inclusion (conjugateSpanBy_le hVW (le_sup_left.trans hJW))) (inclusion_injective _)

/-- The actual span is two-reduced in LR. The core centralizes every
L-conjugate of V, and the outside component survives the centralizer quotient;
the quasisimple-kernel theorem therefore kills its two-core. -/
theorem component_span_isR2 (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (h : Input KnownSimple.IsKnownSimple I d.R (d.MI I) c.L)
    (hθ : theta (d.MI I) = d.Yplus)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hC : centralizer (d.V : Set G) ≤ d.M) :
    IsR2Within (d.componentSpan c.L) (c.L ⊔ d.R) := by
  let J := c.L ⊔ d.R
  let LJ := c.L.subgroupOf J
  let RJ := d.R.subgroupOf J
  let WJ := (d.componentSpan c.L).subgroupOf J
  let N := centralizer (WJ : Set J)
  have hWJ : d.componentSpan c.L ≤ J :=
    conjugateSpanBy_le ((V_le_R d hR).trans le_sup_right)
      (le_sup_left.trans J.le_normalizer)
  have hYN : d.Yplus ≤ normalizer (c.L : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr c.commutator_eq.ge
  have hJW : J ≤ normalizer (d.componentSpan c.L : Set G) :=
    (le_sup_left : J ≤ overgroup d c.L).trans
      (overgroup_normalizes_span d hθ (hR.le.trans inf_le_right) h.normalizes hYN)
  let hn : WJ.Normal := normal_subgroupOf_of_le_normalizer (by
    simpa only [map_subgroupOf_eq_of_le hWJ] using hJW)
  let : IsElementaryAbelian 2 (d.componentSpan c.L) := component_span_elementary d h hR
  refine ⟨hn,IsElementaryAbelian.subgroupOf hWJ,?_⟩
  let : WJ.Normal := hn
  let : LJ.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  let e : LJ ≃* c.L := subgroupOfEquivOfLe (show c.L ≤ J from le_sup_left)
  let : IsQuasisimple (c.L ⧸ pCore 2 c.L) := c.core_quotient_quasisimple
  let : IsQuasisimple (LJ ⧸ pCore 2 LJ) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hcoreFix : J.pCoreIn 2 ≤ centralizer (d.componentSpan c.L : Set G) := by
    apply le_centralizer_iff.mpr
    apply conjugateSpanBy_le
    · exact le_centralizer_iff.mp
        ((component_joinCore_le_radical h).trans (hR.le.trans inf_le_right))
    · exact ((le_sup_left : c.L ≤ J).trans
        (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J
          (pCore 2 J)))).trans (normalizer_le_normalizer_centralizer _)
  have hQN : pCore 2 J ≤ N := by
    intro x hx w hw
    exact Subtype.ext (hcoreFix (mem_map_of_mem J.subtype hx) w hw)
  have hKN : ¬ LJ ≤ N := by
    intro hh
    apply c.outside
    intro l hl
    apply hC
    intro v hv
    have hvW := le_conjugateSpanBy d.V c.L hv
    exact congrArg Subtype.val
      (hh (show (⟨l,mem_sup_left hl⟩ : J) ∈ LJ from hl) ⟨v,hWJ hvW⟩ hvW)
  have hgen : LJ ⊔ RJ = ⊤ := by
    rw [←subgroupOf_sup (show c.L ≤ J from le_sup_left)
      (show d.R ≤ J from le_sup_right),subgroupOf_self]
  exact (QuasisimpleKernel.normal_kernel_structure LJ RJ N
    (h.component.2.subgroupOf_of_le le_sup_left h.join_le)
    (isPGroup_pCoreIn 2 _).comap_subtype hgen hQN hKN).2

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus)
    (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
include hG hempty hM hu hmany hI htwo

/-- The rank-two alternative at one outside member forces the same alternative
at every outside member. This is the uniform earlier input used in 15.3.38. -/
theorem rankTwoCase_uniform (J : Subgroup G) (hJ : J ∈ d.Hplus) :
    OutsideStructure.RankTwoCase d J := by
  exact ComponentIntersection.rank_two_case_of_three_rank_two d J
    (OutsideStructure.source_lemma_15_3_11_from_selection
      hG d hempty hM hu hmany J hJ).local_structure
    (OutsideStructure.rankTwoCase_three_rank hG d hI htwo)

include hf

/-- Both rank-two quotient alternatives supply the literal C.2.7 input. -/
theorem rankTwo_component_input_from_case :
    Input KnownSimple.IsKnownSimple I d.R (d.MI I) c.L :=
  rankTwo_component_input hG d hempty hM hu hmany hI htwo
    (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) hf c

/-- The local geometric portion of 15.3.16, with original earlier-source
hypotheses. The distinct model/parabolic classification assertion is not included. -/
theorem source_lemma_15_3_16_local_geometry :
    IsElementaryAbelian 2 (d.componentSpan c.L) ∧
      c.L = ⁅c.L,Stellmacher.elementaryAbelianMaxJ d.R⁆ ∧
      (c.L ⊔ d.R).pCoreIn 2 ≤ d.R ∧
      KernelConclusion c.L d.R ∧ OffenderConclusion c.L d.R := by
  have h := rankTwo_component_input_from_case hG d hempty hM hu hmany hI htwo hf c
  exact ⟨component_span_elementary d h htwo.2.2.2.2.1,
    component_eq_commutator_thompson h,component_joinCore_le_radical h,
    ChapterC.C27Source.kernel_offender_from_source h⟩

/-- The two-reduced span clause consumed by the four- and five-dimensional
exclusions, with all geometric premises supplied by the original setup. -/
theorem source_lemma_15_3_16_span_isR2 :
    IsR2Within (d.componentSpan c.L) (c.L ⊔ d.R) := by
  have h := rankTwo_component_input_from_case hG d hempty hM hu hmany hI htwo hf c
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  apply component_span_isR2 d c h h11.theta_eq.symm htwo.2.2.2.2.1
  have he := InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1
  exact (Subgroup.centralizer_le_normalizer _).trans he.ge

/-- Original 15.3.15 supplies an actual component with the geometric
clauses of 15.3.16. Only the separate model-classification clause is omitted. -/
theorem exists_rankTwo_component_geometry :
    ∃ c : ComponentWitness d I,
      IsElementaryAbelian 2 (d.componentSpan c.L) ∧
      c.L = ⁅c.L,Stellmacher.elementaryAbelianMaxJ d.R⁆ ∧
      (c.L ⊔ d.R).pCoreIn 2 ≤ d.R ∧
      IsR2Within (d.componentSpan c.L) (c.L ⊔ d.R) := by
  obtain ⟨c⟩ := SourceRankOne.OriginalSource.source_lemma_15_3_26_2
    hG d hempty hM hu hmany hI hf
  obtain ⟨hW,hJ,hQ,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  exact ⟨c,hW,hJ,hQ,source_lemma_15_3_16_span_isR2
    hG d hempty hM hu hmany hI htwo hf c⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

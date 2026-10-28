module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RankOneBlocks
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.SelectedSource
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.RankTwoRank
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.Commutator
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.SourceCases.Sylow
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.ResidualInvariance.LocalActions
public import Theory.GroupTheory.PCoreInRestriction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFiveSylowFixed
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin
public import Theory.SpecificGroups.AlternatingFiveSylowCoreJoin

/-!
# Original15.3.19: excluding the alternating-five block

The nontrivial two-perfect Y_L is normalized by S∩L. Its proper Sylow
overgroup in the actual A₅ quotient identifies its image as A₄. Hence the
component Sylow lies in O₂(L)O₂(Y_L), which original15.3.12 places in R.
Thus R is Sylow in LR without an additional C.2.7 row hypothesis.

The A₅ block splits O₂(LR) as U(L) times its L-centralizer. Since V≤Z(R),
its U-coordinate belongs to the Sylow-fixed line. Y₊ normalizes that line
and therefore fixes it, so [V,Y₊] centralizes L. The original chosen module
W=[W,Y₊] has N_G(W)≤M, contradicting L≰M.

The final theorem applies this exclusion to the literal C.2.7 rank-one
Sylow row, leaving only natural L₂ blocks. The latter source18 exclusion
remains separate. Source: Aschbacher–Smith15.3.11–12 and15.3.19, pp.1123–1127.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Subgroup Theory.GroupTheory ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original component Sylow subgroup lies in the source radical in the A₅ case. -/
theorem alternatingFive_radical_sylow_from_case
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 5)) :
    Chapter1.IsSylowIn 2 d.R (c.L ⊔ d.R) := by
  have hrank := OutsideStructure.rankTwoCase_three_rank hG d hI htwo
  obtain ⟨hne,hRL,hprod⟩ := ComponentIntersection.source_lemma_15_3_12_1_from_selection
    hG d hempty hM hu hmany hI (component_le c)
    (LocalData.thompson_component_in c.le_thompson c.component) hrank c.rank_pos
  obtain ⟨S,hS⟩ := (OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI).sylow
  obtain ⟨P,hP⟩ := LinearThree.Extension.SourceCases.component_sylow d c S hS
  let A := (YL d c.L).subgroupOf c.L
  have hAL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hAM : YL d c.L ≤ d.M :=
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_left).trans
      ((RankTwo.yplus_le_residualY_of_choice d.choice).trans
        (Chapter14.SourcePreliminaries.sourceResidual_le _ _))
  have hAne : A ≠ ⊥ := by
    intro he
    apply hne
    have hh := map_subgroupOf_eq_of_le hAL
    change A.map c.L.subtype = _ at hh
    rw [he,Subgroup.map_bot] at hh
    exact hh.symm
  have hAp : IsPPerfect 2 A :=
    (ComponentIntersection.intersectionResidual_isPPerfect d.Yplus c.L).of_surjective
      (subgroupOfEquivOfLe hAL).symm.toMonoidHom (subgroupOfEquivOfLe hAL).symm.surjective
  have hPA : (P : Subgroup c.L) ≤ normalizer (A : Set c.L) := by
    rw [hP]
    apply le_normalizer_iff.mpr
    intro p hp a ha
    exact (LinearThree.ResidualInvariance.componentSylow_normalizes_YL d c.L
      ⟨hp,p.property⟩ (a : G)).mp ha
  have hproper : A ⊔ (P : Subgroup c.L) ≠ ⊤ := by
    have hle : A ⊔ (P : Subgroup c.L) ≤ d.M.subgroupOf c.L := by
      refine sup_le (fun a ha => hAM ha) ?_
      rw [hP]
      exact fun p hp => d.sylow_le hp.1
    intro he
    apply c.outside
    intro l hl
    exact hle (he ▸ mem_top (⟨l,hl⟩ : c.L))
  have hbound := Theory.SpecificGroups.alternatingFive_sylow_le_core_join e P A hAne hAp hPA hproper
  have hcores : c.L.pCoreIn 2 ⊔ (YL d c.L).pCoreIn 2 ≤ d.R := by
    apply sup_le
    · intro x hx
      exact hprod ⟨x,hx,1,(pCoreIn 2 (YL d c.L)).one_mem,mul_one x⟩
    · intro x hx
      exact hprod ⟨1,(pCoreIn 2 c.L).one_mem,x,hx,one_mul x⟩
  have hmap : (pCore 2 c.L ⊔ A.pCoreIn 2).map c.L.subtype =
      c.L.pCoreIn 2 ⊔ (YL d c.L).pCoreIn 2 := by
    rw [Subgroup.map_sup]
    congr 1
    rw [show A = (YL d c.L).subgroupOf c.L from rfl,pCoreIn_subgroupOf 2 _ _ hAL,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans hAL)]
  exact (isPGroup_pCoreIn 2 (d.Yplus ⊔ d.S)).exists_sylow_sup_of_coprime_index
    c.L d.R hRL (P : Subgroup c.L) P.not_dvd_index
      ((map_mono hbound).trans (hmap.le.trans hcores))
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Subgroup Theory.GroupTheory
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Original 15.3.19's A₅-block exclusion, using the actual radical Sylow
conclusion supplied by the rank-one row of C.2.7. -/
theorem source_15_3_19_alternatingFive_of_radical_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus)
    (htwo : OutsideStructure.RankTwoCase d I) (c : ComponentWitness d I)
    (hRL : d.R ≤ normalizer (c.L : Set G))
    (hSyl : Chapter1.IsSylowIn 2 d.R (c.L ⊔ d.R))
    (hb : ChapterC.IsAlternatingBlock c.L 5) : False := by
  have hQR : (c.L ⊔ d.R).pCoreIn 2 ≤ d.R := by
    obtain ⟨P,hP⟩ := hSyl
    exact (map_mono (pCore_isPGroup.le_sylow_of_normal P)).trans_eq hP
  have hR := htwo.2.2.2.2.1
  have hYL : d.Yplus ≤ normalizer (c.L : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr c.commutator_eq.ge
  have hYR : d.Yplus ≤ normalizer (d.R : Set G) :=
    (le_sup_left : d.Yplus ≤ d.Yplus ⊔ d.S).trans
      ((d.Yplus ⊔ d.S).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (d.Yplus ⊔ d.S) (pCore 2 _)))
  have hVQ : d.V ≤ (c.L ⊔ d.R).pCoreIn 2 := by
    have hc : centralizer (pCore 2 c.L : Set c.L) ≤ pCore 2 c.L := by
      rw [←hb.2.1.fitting]
      exact centralizer_generalizedFitting_le c.L
    have hJc := centralizer_pCore_sup_le 2 c.L d.R hc (isPGroup_pCoreIn 2 _) hRL
    intro v hv
    let x : (c.L ⊔ d.R : Subgroup G) := ⟨v,mem_sup_right (V_le_R d hR hv)⟩
    have hx : x ∈ centralizer (pCore 2 (c.L ⊔ d.R : Subgroup G) : Set _) := by
      intro q hq
      exact Subtype.ext ((V_le_center_R d hR hv).2 q (hQR (mem_map_of_mem _ hq)))
    exact mem_map_of_mem _ (hJc hx)
  have hcomm := ChapterC.IsAlternatingBlock.commutator_le_centralizer_of_sylow_fixed c.L d.R d.Yplus d.V hb hRL hYL
    hYR hSyl hVQ ((V_le_center_R d hR).trans inf_le_right)
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have h7image := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne).1
  have hspan := source_residual_seed_span hG d.T hempty d.action hM hu hmany hne
  have hNV : normalizer (d.V : Set G) = d.M :=
    (InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1).symm
  obtain ⟨W,hchoice,_,_,_,hW,_,hNW,_,_⟩ :=
    OutsideStructure.LocalBranches.chosen_action d I hI h7image hspan hNV
  have hWV : W ≤ d.V := by
    rcases hchoice with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact le_rfl
    · exact d.action.plane_le _
  apply c.outside
  exact ((le_centralizer_iff.mp
    (hW.le.trans ((commutator_mono hWV le_rfl).trans hcomm))).trans
    (Subgroup.centralizer_le_normalizer _)).trans hNW
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Subgroup Theory.GroupTheory ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
/-- Original 15.3.19's A₅-block exclusion. Sylow placement is derived from
original12 and the actual A₅ quotient, including the transposition row. -/
theorem source_15_3_19_alternatingFive
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus)
    (htwo : OutsideStructure.RankTwoCase d I) (c : ComponentWitness d I)
    (hb : ChapterC.IsAlternatingBlock c.L 5) : False := by
  obtain ⟨r,⟨m⟩,hr⟩ := hb.2.2
  have hs := alternatingFive_radical_sylow_from_case hG d hempty hM hu hmany hI htwo c m.quotientIso
  have hrank := OutsideStructure.rankTwoCase_three_rank hG d hI htwo
  have h12 := ComponentIntersection.source_lemma_15_3_12_1_from_selection
    hG d hempty hM hu hmany hI (component_le c)
    (LocalData.thompson_component_in c.le_thompson c.component) hrank c.rank_pos
  exact source_15_3_19_alternatingFive_of_radical_sylow hG d hempty hM hu hmany hI htwo c h12.2.1 hs hb
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Subgroup Theory.GroupTheory ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
/-- The actual rank-one Sylow row of C.2.7 leaves only the natural L₂ block.
The alternating-five case is excluded from the original ambient hypotheses. -/
theorem source_rankOne_block_of_radical_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hs : Chapter1.IsSylowIn 2 d.R (c.L ⊔ d.R)) :
    ∃ n, ChapterC.IsL2EvenBlock c.L n := by
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  rcases ChapterC.C27Source.source_rankOne_blocks_of_sylow h hs with hn | h5
  · exact hn
  · exact (source_15_3_19_alternatingFive hG d hempty hM hu hmany hI htwo c h5).elim
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

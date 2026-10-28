module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankOneResidual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankOneTorus
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverSylowCommutator
/-!
# The block module lies in the intersection residual's two-core

The actual component Sylow normalizes Y_L and has proper join with Y_L.
Its field-four quotient identifies the Sylow image in the two-core of
Y_L, so P≤O₂(L)O₂(Y_L). The natural-cover central-layer theorem and the
actual cubic part of Y_L then give U(L)≤O₂(Y_L). All subgroup restrictions
and core images use the original selected component and ambient inclusion.

Source: Aschbacher–Smith15.3.18, printed pp.1126–1127, using I.2.3(3)
and the residual geometry of15.3.11–12.
-/
public section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Subgroup Theory.GroupTheory ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Original15.3.18's two-core placement for the actual field-four block. -/
theorem naturalFour_blockU_le_YL_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (c : ComponentWitness d I) (hb : ChapterC.IsL2EvenBlock c.L 2) :
    (ChapterC.blockU c.L).map c.L.subtype ≤ (YL d c.L).pCoreIn 2 := by
  obtain ⟨e⟩ := hb.four_quotient_alternatingFive
  have hrank := OutsideStructure.rankTwoCase_three_rank hG d hI htwo
  obtain ⟨hne,_,_⟩ := ComponentIntersection.source_lemma_15_3_12_1_from_selection
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
  have hcA : 3^(Nat.card A).factorization 3 = 3 := by
    have hc := (naturalFour_source_local_geometry hG d hempty hM hu hmany hI htwo c hb).2.2.2.2.1
    rwa [←Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv] at hc
  have hU := hb.blockU_le_normalized_core P A hPA hbound hcA
  have hh := map_mono (f := c.L.subtype) hU
  rw [show A = (YL d c.L).subgroupOf c.L from rfl,pCoreIn_subgroupOf 2 _ _ hAL,
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans hAL)] at hh
  exact hh

/-- The marked original rank-one case supplies the two-core placement
without an additional field-degree or natural-cover hypothesis. -/
theorem source_15_3_18_blockU_le_YL_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hSyl : Chapter1.IsSylowIn 2 d.R (c.L ⊔ d.R))
    (hborel : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.IsRankOneBorel
      (Chapter1.RadicalExclusions.ModelReduction.starImage c.L d.R c.L)
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.starM c.L d.R (d.MI I)))
    {n : ℕ} (hn : ChapterC.IsL2EvenBlock c.L n) :
    (ChapterC.blockU c.L).map c.L.subtype ≤ (YL d c.L).pCoreIn 2 := by
  have hdegree := source_15_3_18_field_degree hG d hempty hM hu hmany hI htwo hf c hSyl hborel hn
  subst n
  exact naturalFour_blockU_le_YL_core hG d hempty hM hu hmany hI htwo c hn

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

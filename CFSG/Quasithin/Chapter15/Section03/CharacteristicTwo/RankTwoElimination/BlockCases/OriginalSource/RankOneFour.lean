module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankOneFactors
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankOneTorusCore
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.FixedLayerCentralizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.ConjugatePair
/-!
# Original15.3.18 and the marked rank-one exclusion

For the field-four block, the two residual factors act on the two original
orthogonal planes. The complementary residual fixes a noncentral part
of the short layer and therefore centralizes L. The actual block layer
lies in O₂(Y_L); its conjugate lies in Y_C. Thus L and S normalize their
conjugate pair, and uniqueness of the maximal two-local overgroup of YT
contradicts L being outside M.

The final consumer uses the literal radical Sylow and marked Borel outputs
of the rank-one C.2.7 row. Concrete block recognition and the A₅ alternative
are discharged internally, retaining all original ambient hypotheses.
Source: Aschbacher–Smith15.3.18–19, printed pp.1126–1127.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open RankTwo ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual complementary cubic residual centralizes the field-four component. -/
theorem naturalFour_source_YC_centralizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hb : ChapterC.IsL2EvenBlock c.L 2) :
    YC d c.L ≤ centralizer (c.L : Set G) := by
  obtain ⟨_,hfac,_⟩ := naturalFour_source_residual_factors
    hG d hempty hM hu hmany hI htwo hf c hb
  obtain ⟨hneMc,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have h7 := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hneMc).1
  have hm := LinearThree.movingPlane_geometry d c.L h7 hfac
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have hC : centralizer (d.V : Set G) ≤ d.M :=
    (Subgroup.centralizer_le_normalizer _).trans
      (InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1).ge
  have hW := RankTwoElimination.OriginalSource.source_lemma_15_3_16_span_isR2
    hG d hempty hM hu hmany hI htwo hf c
  have hWL : d.componentSpan c.L ≤ c.L ⊔ d.R :=
    conjugateSpanBy_le ((V_le_R d htwo.2.2.2.2.1).trans le_sup_right)
      (le_sup_left.trans (c.L ⊔ d.R).le_normalizer)
  have hU := natural_block_support d c h.normalizes hW hWL hC hb.2.1
  have hAL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hEU : LinearThree.movingPlane d c.L ≤ (ChapterC.blockU c.L).map c.L.subtype := by
    rw [hU]
    exact commutator_mono (le_conjugateSpanBy _ _) hAL
  have hne : ¬ LinearThree.movingPlane d c.L ≤ centralizer (c.L : Set G) := by
    intro hc
    have he : LinearThree.movingPlane d c.L = ⊥ := le_bot_iff.mp
      ((le_inf le_rfl (hc.trans (centralizer_le hAL))).trans hm.2.2.2.2.le)
    have hc := hm.1
    simp [he] at hc
  have hc := (Chapter4.le_sectionCentralizer_iff (YC d c.L) c.L).mp
    ((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_right)
  exact hb.2.1.centralizes_of_coreQuotient_and_noncentral_fixed c.L (YC d c.L)
    (LinearThree.movingPlane d c.L) (ComponentIntersection.centralizerResidual_isPPerfect _ _)
    hc.1 hc.2 hEU (le_centralizer_iff.mp hm.2.2.2.1) hne

/-- The original field-four branch ends in the conjugate-pair normalizer contradiction. -/
theorem source_15_3_18_naturalFour
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hb : ChapterC.IsL2EvenBlock c.L 2) : False := by
  obtain ⟨hfirst,hfac,hSL⟩ := naturalFour_source_residual_factors
    hG d hempty hM hu hmany hI htwo hf c hb
  have hYC := naturalFour_source_YC_centralizes hG d hempty hM hu hmany hI htwo hf c hb
  have hUcore := naturalFour_blockU_le_YL_core hG d hempty hM hu hmany hI htwo c hb
  let U := (ChapterC.blockU c.L).map c.L.subtype
  have hSU : d.S ≤ normalizer (U : Set G) :=
    hSL.trans (normalizer_le_normalizer_characteristic_image c.L (ChapterC.blockU c.L))
  have hLU : c.L ≤ normalizer (U : Set G) :=
    c.L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image c.L (ChapterC.blockU c.L))
  have hAL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hrank := OutsideStructure.rankTwoCase_three_rank hG d hI htwo
  have h12 := ComponentIntersection.source_lemma_15_3_12_1_from_selection
    hG d hempty hM hu hmany hI (component_le c)
    (LocalData.thompson_component_in c.le_thompson c.component) hrank c.rank_pos
  have hcoreR : (YL d c.L).pCoreIn 2 ≤ d.R := by
    intro x hx
    exact h12.2.2 ⟨1,(pCoreIn 2 c.L).one_mem,x,hx,one_mul x⟩
  have hRS : d.R ≤ d.S := by
    rw [htwo.2.2.2.2.1]
    exact le_inf inf_le_left (inf_le_right.trans
      ((centralizer_le (d.action.plane_le 1)).trans (Subgroup.centralizer_le_normalizer _)))
  have hUS : U ≤ d.S := hUcore.trans (hcoreR.trans hRS)
  have hUne : U ≠ ⊥ := by
    intro he
    have hbot : ChapterC.blockU c.L = ⊥ := (map_eq_bot_iff_of_injective _ c.L.subtype_injective).mp he
    exact hb.2.1.blockU_ne_bot hbot
  have hindex := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hnot : ¬ (d.T : Subgroup G) ≤ d.S := by
    intro ht
    have he : d.S.subgroupOf (d.T : Subgroup G) = ⊤ := subgroupOf_eq_top.mpr ht
    rw [he,index_top] at hindex
    norm_num at hindex
  obtain ⟨t,ht,htS⟩ := Set.not_subset.mp hnot
  have hex := LinearThree.residual_factors_exchanged d c.L hfac t ht htS
  have hUt : U.conjBy t ≤ YC d c.L := by
    rw [←hex]
    exact map_mono (hUcore.trans (pCoreIn_le 2 _))
  have hLut : c.L ≤ normalizer (U.conjBy t : Set G) :=
    ((le_centralizer_iff.mp hYC).trans (centralizer_le hUt)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hindex)
  have hSt : d.S.conjBy t = d.S := mem_normalizer_iff_map_conj_eq.mp (hTS ht)
  have hSut : d.S ≤ normalizer (U.conjBy t : Set G) := by
    have hm := (map_mono (f := (MulAut.conj t).toMonoidHom) hSU).trans
      (U.le_normalizer_map (MulAut.conj t).toMonoidHom)
    change d.S.conjBy t ≤ _ at hm
    rwa [hSt] at hm
  have hLS : c.L ⊔ d.S ≤ normalizer (conjugatePair U t : Set G) :=
    (le_inf (sup_le hLU hSU) (sup_le hLut hSut)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hY : d.Y ≤ c.L ⊔ (d.T : Subgroup G) := by
    rw [←hfirst,(naturalFour_source_local_geometry hG d hempty hM hu hmany hI htwo c hb).2.1]
    apply sup_le (hAL.trans le_sup_left)
    rw [←hex]
    rintro _ ⟨y,hy,rfl⟩
    exact ((c.L ⊔ (d.T : Subgroup G)).le_normalizer (mem_sup_right ht) y).mp
      (mem_sup_left (hAL hy))
  obtain ⟨hneMc,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have huYT := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hneMc).2.2.2.2.1
  exact outside_conjugatePair_contradiction d c.outside hUne hUS t ht htS hindex hSU hLS hY huYT

/-- Original15.3.18, with the literal Sylow and Borel conclusions supplied
by the actual rank-one C.2.7 row. -/
theorem source_15_3_18_natural
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
    {n : ℕ} (hn : ChapterC.IsL2EvenBlock c.L n) : False := by
  have hd := source_15_3_18_field_degree hG d hempty hM hu hmany hI htwo hf c hSyl hborel hn
  subst n
  exact source_15_3_18_naturalFour hG d hempty hM hu hmany hI htwo hf c hn

/-- The actual marked C.2.7 rank-one row is impossible in source15.3.13. -/
theorem source_rankOne_row_exclusion
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
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.starM c.L d.R (d.MI I))) : False := by
  obtain ⟨n,hn⟩ := source_rankOne_block_of_radical_sylow hG d hempty hM hu hmany hI htwo hf c hSyl
  exact source_15_3_18_natural hG d hempty hM hu hmany hI htwo hf c hSyl hborel hn
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

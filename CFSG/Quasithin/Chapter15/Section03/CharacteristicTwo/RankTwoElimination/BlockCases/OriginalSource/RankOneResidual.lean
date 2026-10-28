module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankOneA5
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2OddFixed
public import Theory.SpecificGroups.AlternatingFiveBorelProjection
/-!
# The two cubic residuals in the actual field-four component

The A₅ core quotient has three-rank one. A two-perfect subgroup of its
automorphism group acts by inner automorphisms, so original15.3.12 gives
the product of the two component residuals and their literal E₉ quotient.
The actual natural L₂(4) block supplies both this quotient marking and
the radical Sylow placement, with no additional action assumption.

Source: Aschbacher–Smith15.3.18, pp.1126–1127. The moving-plane and
conjugate-pair arguments are separate consumers of this preparation.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open ComponentIntersection ComponentIntersection.InnerSplitting RankTwo ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem alternatingFive_component_rank {I : Subgroup G} (d : LocalData G)
    (c : ComponentWitness d I) (e : (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 5)) :
    primeRank 3 c.L = 1 := by
  apply le_antisymm ?_ c.rank_pos
  rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 c.L) pCore_isPGroup,
    primeRank_congr 3 e]
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let : IsElementaryAbelian 3 E := hE
  have hd : Nat.card E ∣ 3*20 := by
    have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    simpa only [hcard] using E.card_subgroup_dvd_card
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hp : Nat.Coprime (Nat.card E) 20 := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 20).pow_left n
  exact Nat.le_of_dvd (by decide) (hp.dvd_mul_right.mp hd)

omit [Finite G] in
private theorem alternatingFive_inner_on_quotient {Y L : Subgroup G}
    (hn : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    InducesInnerOnTwoCoreQuotient Y L := by
  let a := (sectionAction L).comp (inclusion hn)
  obtain ⟨f,hf⟩ := AlternatingFiveProjection.exists_inner_lift hp a e
  intro y hy
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (f ⟨y,hy⟩)
  refine ⟨l,l.property,?_⟩
  apply (sectionAction_eq_one_iff L
    ((inclusion L.le_normalizer l)⁻¹ * inclusion hn ⟨y,hy⟩)).mp
  rw [map_mul,map_inv,sectionAction_on_component]
  apply inv_mul_eq_one.mpr
  have hh := DFunLike.congr_fun hf ⟨y,hy⟩
  change MulAut.conj (f ⟨y,hy⟩) = a ⟨y,hy⟩ at hh
  exact (congrArg MulAut.conj hl).trans hh

/-- The actual field-four component has both residual cubic directions,
with their literal E₉ quotient, before any first-choice reduction. -/
theorem naturalFour_residual_split
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (c : ComponentWitness d I) (e : (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 5)) :
    d.Yplus = YL d c.L ⊔ YC d c.L ∧
      Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9 ∧
      Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* ElementaryNine) ∧
      3^(Nat.card (YL d c.L)).factorization 3 = 3 ∧
      3^(Nat.card (YC d c.L)).factorization 3 = 3 := by
  have hn : d.Yplus ≤ normalizer (c.L : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr c.commutator_eq.ge
  have hi := alternatingFive_inner_on_quotient hn (yplus_perfect_of_choice d.choice) e
  obtain ⟨hprod,_,h9,_,he9,hL,hC⟩ :=
    source_lemma_15_3_12_2_three_parts_from_selection hG d hempty hM hu hmany hI
      (component_le c) (LocalData.thompson_component_in c.le_thompson c.component)
      (OutsideStructure.rankTwoCase_three_rank hG d hI htwo)
      (alternatingFive_component_rank d c e) hi
  refine ⟨le_antisymm ?_ (sup_le
    ((intersectionResidual_le _ _).trans inf_le_left)
    ((centralizerResidual_le _ _).trans inf_le_left)),h9,he9,hL,hC⟩
  intro y hy
  change y ∈ (d.Yplus : Set G) at hy
  rw [hprod] at hy
  obtain ⟨a,ha,b,hb,rfl⟩ := hy
  exact mul_mem_sup ha hb
/-- The literal field-four source18 case supplies the radical Sylow placement
and both cubic residual directions without an additional action hypothesis. -/
theorem naturalFour_source_local_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (c : ComponentWitness d I) (hb : ChapterC.IsL2EvenBlock c.L 2) :
    Chapter1.IsSylowIn 2 d.R (c.L ⊔ d.R) ∧
      d.Yplus = YL d c.L ⊔ YC d c.L ∧
      Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9 ∧
      Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* ElementaryNine) ∧
      3^(Nat.card (YL d c.L)).factorization 3 = 3 ∧
      3^(Nat.card (YC d c.L)).factorization 3 = 3 := by
  obtain ⟨e⟩ := hb.four_quotient_alternatingFive
  exact ⟨alternatingFive_radical_sylow_from_case hG d hempty hM hu hmany hI htwo c e,
    naturalFour_residual_split hG d hempty hM hu hmany hI htwo c e⟩
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

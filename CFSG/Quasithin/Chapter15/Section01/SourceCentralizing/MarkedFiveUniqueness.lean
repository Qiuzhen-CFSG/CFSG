module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SmallActionUniqueness
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonActors
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.TwoRank
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.TwoSubgroups
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonPrepared
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralFiveSetup
public import Theory.GroupTheory.NormalTenOvergroup
public import Theory.GroupAction.FixedSubgroupImageNormalizer

/-!
# The marked-five row of original15.2.5

A third maximal two-local subgroup induces an action containing the marked
order-ten subgroup, or normalizes the image of J₁(T). In the first case the
original residual seed-span forces the third subgroup to equal M. In the
second, it normalizes C_V(J₁(T)), and original15.1.14 places it in Mc.
The earlier residual-centralization premise remains explicit; every other
input is supplied from the original standing hypotheses and chosen marking.

Source: Aschbacher--Smith15.1.13--14 and15.2.5, printed pp.1091--1092,1107.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped ENNReal IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

private theorem fixed_normalizer_of_thompson_image
    (T : Sylow 2 G) {M V X : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hV : PreparedChosenModule T M V) (hXM : X ≤ M)
    (hn : (X.subgroupOf M).map (actionHom M V hV.normalized).rangeRestrict ≤
      normalizer (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hV.normalized).rangeRestrict : Set _)) :
    X ≤ normalizer (thompsonFixed T V : Set G) := by
  let f := (actionHom M V hV.normalized).rangeRestrict
  let J := ChapterB.thompsonJ (T : Subgroup G) 1
  have hJM : J ≤ M := (ChapterB.thompsonJ_le _ _).trans hTM
  let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hV.normalized
  have hker : f.ker ≤ centralizer (V.subgroupOf M : Set M) := by
    intro x hx v hv
    have hx' : x ∈ (actionHom M V hV.normalized).ker := congrArg Subtype.val hx
    rw [actionHom_ker] at hx'
    exact Subtype.ext (hx' v hv)
  have he : V.subgroupOf M ⊓ centralizer (J.subgroupOf M : Set M) =
      (thompsonFixed T V).subgroupOf M := by
    ext x
    constructor
    · rintro ⟨hx,hc⟩
      refine ⟨hx,?_⟩
      intro j hj
      exact congrArg M.subtype (hc ⟨j,hJM hj⟩ hj)
    · rintro ⟨hx,hc⟩
      exact ⟨hx,fun j hj => Subtype.ext (hc j hj)⟩
  have hh := normalizes_fixed_of_image_normalizes f (V.subgroupOf M) (J.subgroupOf M)
    (X.subgroupOf M) le_normalizer_of_normal hker hn
  rw [he,←subgroupOf_normalizer_eq (inf_le_left.trans hV.le_selected)] at hh
  intro x hx
  exact hh (show (⟨x,hXM hx⟩ : M) ∈ X.subgroupOf M from hx)

private theorem cubic_ratio_of_Jhat_card_ten
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hq : quadraticRatio ρ = 2) (hK : Nat.card (Jhat ρ) = 10) : cubicRatio ρ = 2 := by
  let K := Jhat ρ
  have hstar : (QhatStar ρ).Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    have hz : K = ⊥ := by simp [K,Jhat,he]
    have hh : Nat.card K = 1 := by rw [hz]; simp
    have hh' : Nat.card (Jhat ρ) = 1 := hh
    omega
  obtain ⟨B,hB⟩ := hstar
  have hrB : rank B = 1 := by
    have hlo := hB.1.2.1.rank_pos
    have hhigh : rank B ≤ 1 := by
      by_contra! hh
      have hdiv : 4 ∣ Nat.card B := by
        rw [hB.1.2.1.card_eq_two_pow_rank]
        exact pow_dvd_pow 2 (by omega : 2 ≤ rank B)
      have hdiv' := hdiv.trans (card_dvd_of_le (show B ≤ K from le_sSup hB))
      rw [hK] at hdiv'
      norm_num at hdiv'
    omega
  have hq3 : cubicRatio ρ = 2 := by
    rcases QhatStar.ratio_one_or_two_of_rank_one ρ
      hf hB hrB with h1 | h2
    · have hh := (cubicRatio_le_one_iff_quadraticRatio_le_one ρ).mp h1.le
      rw [hq] at hh
      norm_num at hh
    · exact h2
  exact hq3

private theorem marked_five_thompson_image_of_movement
    (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((UniqueFactor.imageRepresentation M V hV.normalized).comp
      (ChapterD.Jhat (UniqueFactor.imageRepresentation M V hV.normalized)).subtype))
    (hd : DihedralMarking l 5 2)
    (hm : ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ ≠ ⊥) :
    let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict
    Nat.card R = 2 ∧ R ≤ Jhat (UniqueFactor.imageRepresentation M V hV.normalized) := by
  classical
  let ρ := UniqueFactor.imageRepresentation M V hV.normalized
  let D := internalActionImage M V hV.normalized
  let K := Jhat ρ
  let f : M →* D := (actionHom M V hV.normalized).rangeRestrict
  let J := ChapterB.thompsonJ (T : Subgroup G) 1
  let R := (J.subgroupOf M).map f
  let S := ((T : Subgroup G).subgroupOf M).map f
  let : K.Normal := Jhat_normal ρ
  have hp : PrimeDimensionOptions 5 2 :=
    (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  have hK : Nat.card K = 10 := by
    simpa using (hd.ambient_marks K hp).1
  have hnR := chosen_thompson_image_ne_bot (T : Subgroup G) M V hM.1.2 hV.normalized hm
  have hq3 := cubic_ratio_of_Jhat_card_ten ρ
    (UniqueFactor.imageRepresentation_injective _ _ _) hV.quadratic_ratio hK
  have hrank := hd.ambient_twoRank_le_two (UniqueFactor.imageRepresentation_injective _ _ _) K hp
  have ha := chosen_sylow_thompson_actors T hM.1.2 hV.le_selected hV.normalized
    hV.quadratic_ratio hq3 (fun E hE => hE.rank_le_of_primeRank_le hrank)
  have hRK : R ≤ K :=
    (chosen_thompson_image_le_Jhat (T : Subgroup G) M V hM.1.2 hV.normalized
      (fun A hA hB => (ha A hA hB).2.2.2)).trans inf_le_right
  have hRS : R ≤ S := map_mono (subgroupOf_mono M (ChapterB.thompsonJ_le _ _))
  have hR : Nat.card R = 2 := by
    have hb := l.two_subgroup_inf_card_le_two K S ((T.subtype hM.1.2).isPGroup'.map f)
    have hr := (card_le_of_le (le_inf hRS hRK)).trans hb
    have hl := (one_lt_card_iff_ne_bot R).mpr hnR
    omega
  exact ⟨hR,hRK⟩

/-- The marked-five row, retaining precisely the earlier global residual premise. -/
theorem PreparedChosenModule.maximal_overgroups_of_marked_five
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((UniqueFactor.imageRepresentation M V hV.normalized).comp
      (ChapterD.Jhat (UniqueFactor.imageRepresentation M V hV.normalized)).subtype))
    (hd : DihedralMarking l 5 2)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc} := by
  classical
  let ρ := UniqueFactor.imageRepresentation M V hV.normalized
  let D := internalActionImage M V hV.normalized
  let K := Jhat ρ
  let f : M →* D := (actionHom M V hV.normalized).rangeRestrict
  let J := ChapterB.thompsonJ (T : Subgroup G) 1
  let R := (J.subgroupOf M).map f
  let : K.Normal := Jhat_normal ρ
  have hp : PrimeDimensionOptions 5 2 :=
    (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  have hK : Nat.card K = 10 := by simpa using (hd.ambient_marks K hp).1
  have hm : ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ ≠ ⊥ :=
    (hV.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  obtain ⟨hR,hRK⟩ := marked_five_thompson_image_of_movement T hM hV l hd hm
  have hnormalizer := (hV.thompsonFixed_normalizers hG T hM hJ hu hres).2.1
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  ext N
  constructor
  · intro hN
    by_cases hNM : N = M
    · simp [hNM]
    by_cases hNMc : N = Mc
    · simp [hNMc]
    let H := M ⊓ N
    let A := (H.subgroupOf M).map f
    have hTH : (T : Subgroup G) ≤ H := le_inf hM.1.2 hN.2
    have hRA : R ≤ A := map_mono (subgroupOf_mono M ((ChapterB.thompsonJ_le _ _).trans hTH))
    rcases contains_or_normalizes_of_normal_ten K R A hK hR hRK hRA with hKA | hAN
    · let Y := Section02.caseIIResidual T M (Section02.chosenStarredPreimage M V hV.normalized) Mc
      have hYM : Y ≤ M := Section02.source_caseIIResidual_le T hM.1.2 (map_subtype_le _)
      have hYspan := Section02.source_dihedral_five_residual_seed_span
        hG T hempty hM hJ hu hmany hV l hp hd
      have himage : (Y.subgroupOf M).map f ≤ A := by
        have he := Section02.source_dihedral_caseIIResidual_image hG T hempty hM hJ hu hmany hV l hp hd
        exact he.le.trans ((map_subtype_le _).trans hKA)
      have himage' : (Y.subgroupOf M).map (actionHom M V hV.normalized) ≤
          (H.subgroupOf M).map (actionHom M V hV.normalized) := by
        rintro _ ⟨y,hy,rfl⟩
        obtain ⟨x,hx,he⟩ := himage (mem_map_of_mem f hy)
        exact ⟨x,hx,congrArg Subtype.val he⟩
      have huniq := Section02.source_unique_overgroup_of_action_image hG T hempty hM hJ hV
        hTH inf_le_left hYM hYspan himage'
      exact (hNM (Set.mem_singleton_iff.mp (huniq ▸
        (show N ∈ maximalTwoLocalOvergroups H from ⟨hN.1,inf_le_right⟩)))).elim
    · have hHMc : H ≤ Mc :=
        (fixed_normalizer_of_thompson_image T hM.1.2 hV inf_le_left hAN).trans hnormalizer
      have ho := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
      have hle : N ≤ Mc := by
        intro x hx
        obtain ⟨a,ha,b,hb,rfl⟩ := ho x hx
        exact Mc.mul_mem (hHMc ⟨ha.2,ha.1⟩)
          (localModule_centralizer_le_partner T N hu hb.2)
      exact (hNMc (le_antisymm hle (hN.1.2 hMc.1.1 hle))).elim
  · intro hN
    rcases Set.mem_insert_iff.mp hN with rfl | hN
    · exact hM.1
    · obtain rfl := Set.mem_singleton_iff.mp hN
      exact ⟨hMc.1,hTMc⟩
end CFSG.Quasithin.Chapter15.Section01

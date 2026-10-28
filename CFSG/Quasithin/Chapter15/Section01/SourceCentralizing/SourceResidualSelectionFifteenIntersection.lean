module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.MarkedFiveUniqueness
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.OmegaIntersection
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveFinalQuotient
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ResidualDirectAssembly

/-!
# Third intersections in the original marked-five row

The marked-five H-star wreath quotients force a third maximal two-local
unless the original chosen source is already contradictory. Its intersection
with M cannot contain the marked J-hat in its action image: the original
quintic residual would then supply the full central-seed span and force
uniqueness. The order-ten subgroup calculation therefore makes that image
normalize the literal order-two Thompson image. In the ambient group the
same intersection normalizes C_V(J₁(T)), while escaping the partner Mc.

These conclusions use no global Thompson residual premise. In particular,
normalization of the fixed subgroup is not promoted to placement in Mc.
The cyclic-fifteen and full-module hypotheses are not needed for this step.

Source: Aschbacher--Smith 15.1.13, 15.2.2, 15.2.5 and 15.2.8,
printed pp.1090--1091, 1104 and 1107--1110.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped ENNReal IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
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

/-- The actual marked-five Thompson image has order two and lies in J-hat. -/
theorem ChosenSmallSource.marked_five_thompson_image
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2) :
    letI := h.prepared.elementary
    let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.prepared.normalized).rangeRestrict
    Nat.card R = 2 ∧ R ≤ Jhat (imageRepresentation M V h.prepared.normalized) := by
  let := h.prepared.elementary
  obtain ⟨l,hd⟩ := hd
  exact marked_five_thompson_image_of_movement T h.maximal h.prepared l hd
    (h.prepared.source_thompson_escape_and_movement h.ambient T h.empty h.maximal
      h.many h.centralizing).2

/-- An intersection with a distinct maximal local cannot cover the marked J-hat. -/
theorem ChosenSmallSource.marked_five_third_image_not_contains
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) :
    letI := h.prepared.elementary
    ¬ Jhat (imageRepresentation M V h.prepared.normalized) ≤
      ((M ⊓ N).subgroupOf M).map (actionHom M V h.prepared.normalized).rangeRestrict := by
  let := h.prepared.elementary
  obtain ⟨l,hd⟩ := hd
  intro hKA
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  let H := M ⊓ N
  let A := (H.subgroupOf M).map f
  let Y := caseIIResidual T M (chosenStarredPreimage M V h.prepared.normalized) Mc
  have hp : PrimeDimensionOptions 5 2 :=
    (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  have hYM : Y ≤ M := source_caseIIResidual_le T h.maximal.1.2 (map_subtype_le _)
  have hYspan := source_dihedral_five_residual_seed_span h.ambient T h.empty h.maximal
    h.centralizing h.partner h.many h.prepared l hp hd
  have himage : (Y.subgroupOf M).map f ≤ A := by
    have he := source_dihedral_caseIIResidual_image h.ambient T h.empty h.maximal
      h.centralizing h.partner h.many h.prepared l hp hd
    exact he.le.trans ((map_subtype_le _).trans hKA)
  have himage' : (Y.subgroupOf M).map (actionHom M V h.prepared.normalized) ≤
      (H.subgroupOf M).map (actionHom M V h.prepared.normalized) := by
    rintro _ ⟨y,hy,rfl⟩
    obtain ⟨x,hx,he⟩ := himage (mem_map_of_mem f hy)
    exact ⟨x,hx,congrArg Subtype.val he⟩
  have huniq := source_unique_overgroup_of_action_image h.ambient T h.empty h.maximal
    h.centralizing h.prepared (le_inf h.maximal.1.2 hN.2) inf_le_left hYM hYspan himage'
  exact hNM (Set.mem_singleton_iff.mp (huniq ▸
    (show N ∈ maximalTwoLocalOvergroups H from ⟨hN.1,inf_le_right⟩)))

/-- The third intersection normalizes the literal Thompson-fixed subgroup
and still escapes Mc; no global residual placement is assumed. -/
theorem ChosenSmallSource.marked_five_third_intersection
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    letI := h.prepared.elementary
    let f := (actionHom M V h.prepared.normalized).rangeRestrict
    let A := ((M ⊓ N).subgroupOf M).map f
    let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
    ¬ M ⊓ N ≤ Mc ∧ ¬ Jhat (imageRepresentation M V h.prepared.normalized) ≤ A ∧
      A ≤ normalizer (R : Set _) ∧ M ⊓ N ≤ normalizer (thompsonFixed T V : Set G) := by
  let := h.prepared.elementary
  let ρ := imageRepresentation M V h.prepared.normalized
  let K := Jhat ρ
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  let A := ((M ⊓ N).subgroupOf M).map f
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let : K.Normal := Jhat_normal ρ
  have hnot := h.marked_five_third_image_not_contains hd hN hNM
  obtain ⟨hR,hRK⟩ := h.marked_five_thompson_image hd
  obtain ⟨l,hl⟩ := hd
  have hp : PrimeDimensionOptions 5 2 :=
    (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  have hK : Nat.card K = 10 := by simpa using (hl.ambient_marks K hp).1
  have hRA : R ≤ A := map_mono (subgroupOf_mono M
    ((ChapterB.thompsonJ_le _ _).trans (le_inf h.maximal.1.2 hN.2)))
  have hAN : A ≤ normalizer (R : Set _) :=
    (contains_or_normalizes_of_normal_ten K R A hK hR hRK hRA).resolve_left hnot
  refine ⟨(h.prepared.third_maximal_action_constraints h.ambient T h.empty h.maximal
    h.centralizing h.partner hN hNM hNMc).1,hnot,hAN,?_⟩
  exact fixed_normalizer_of_thompson_image T h.maximal.1.2 h.prepared inf_le_left hAN

/-- A marked-five chosen source forces a third maximal two-local: if only
the chosen pair existed, its proved wreath quotients would contradict the source. -/
theorem ChosenSmallSource.exists_third_of_marked_five
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2) :
    ∃ N ∈ maximalTwoLocalOvergroups (T : Subgroup G), N ≠ M ∧ N ≠ Mc := by
  classical
  by_contra hn
  have htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc} := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton Mc
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
      exact (hn ⟨N,hN,hNM,hNMc⟩).elim
    · intro hN
      rcases Set.mem_insert_iff.mp hN with rfl | hN
      · exact h.maximal.1
      · obtain rfl := Set.mem_singleton_iff.mp hN
        exact ⟨hMc.1,hTMc⟩
  exact source_chosen_contradiction_of_wreath_quotients h htwo
    (fun _ hH => h.HStar_wreath_of_marked_five hd hH)

/-- The actual marked-five source has a third intersection normalizing its
Thompson-fixed subgroup while escaping the distinguished partner. -/
theorem ChosenSmallSource.exists_third_fixed_normalizer_of_marked_five
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2) :
    ∃ N ∈ maximalTwoLocalOvergroups (T : Subgroup G), N ≠ M ∧ N ≠ Mc ∧
      ¬ M ⊓ N ≤ Mc ∧ M ⊓ N ≤ normalizer (thompsonFixed T V : Set G) := by
  obtain ⟨N,hN,hNM,hNMc⟩ := h.exists_third_of_marked_five hd
  have hc := h.marked_five_third_intersection hd hN hNM hNMc
  exact ⟨N,hN,hNM,hNMc,hc.1,hc.2.2.2⟩

end CFSG.Quasithin.Chapter15.Section02


module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialModel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.SourceSelection.Original
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.OmegaIntersection
public import Theory.GroupAction.FixedSubgroupImageNormalizer

/-!
# Original extraspecial intersections normalize the Thompson fixed subgroup

The original Thompson image is an involution of fixed codimension two.
Every proper Sylow overgroup in the extraspecial action is contained in the
central-cubic supplement, so it normalizes this literal image. Pulling the
action normalizer back proves that an intersection with any third maximal
two-local normalizes the original Thompson fixed subgroup. Its action
image has index nine. No global Thompson residual premise is used.

Source: Aschbacher--Smith 15.1.13--14, printed pp.1090--1091.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The actual original Thompson image is the small involution in the extraspecial row. -/
theorem PreparedChosenModule.extraspecial_small_thompson_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    letI := h.elementary
    let ρ := imageRepresentation M V h.normalized
    let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict
    ∃ t : internalActionImage M V h.normalized,
      orderOf t = 2 ∧ zpowers t = R ∧ fixedCodim ρ R = 2 := by
  let := h.elementary
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* internalActionImage M V h.normalized := (actionHom M V h.normalized).rangeRestrict
  let J := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  have hq := ExtraspecialMarker.source_cubic_ratio ρ (imageRepresentation_injective M V h.normalized)
    h.quadratic_ratio _ hex
  obtain ⟨l,_,_,hP,hcard,_,_,_⟩ := hex
  let := hP
  have hcore : pCore 2 D = ⊥ := by
    subst V
    exact source_localAction_twoCore hG T hM
  have hrank := twoRank_le_two_of_extraspecial_twoResidual hcore hcard
  have ha := chosen_sylow_thompson_actors T hM.1.2 h.le_selected h.normalized
    h.quadratic_ratio hq (fun E hE => hE.rank_le_of_primeRank_le hrank)
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hjne := chosen_thompson_image_ne_bot _ _ _ hM.1.2 h.normalized hm
  have hjle := chosen_thompson_image_le_Jhat _ _ _ hM.1.2 h.normalized
    (fun A hA hB => (ha A hA hB).2.2.2)
  have hbound := l.two_subgroup_inf_card_le_two (Jhat ρ)
    (((T : Subgroup G).subgroupOf M).map f) ((T.subtype hM.1.2).isPGroup'.map f)
  have hjcard : Nat.card J = 2 := by
    have hlo := (one_lt_card_iff_ne_bot _).mpr hjne
    have hhi := (card_le_of_le hjle).trans hbound
    change 1 < Nat.card J at hlo
    change Nat.card J ≤ 2 at hhi
    omega
  obtain ⟨A,hA,hB⟩ := exists_chosen_thompson_actor_of_moves _ _ _ hM.1.2 h.normalized hm
  have hb := ha A hA hB
  have hBJ : (A.subgroupOf M).map f ≤ J := map_mono (subgroupOf_mono M (le_sSup hA))
  have hbcard : Nat.card ((A.subgroupOf M).map f) = 2 := hb.1
  have he : (A.subgroupOf M).map f = J := eq_of_le_of_card_ge hBJ (by rw [hbcard,hjcard])
  obtain ⟨t,ht,htJ⟩ := CyclicSource.starred_generator ρ hb.2.2.2 hb.2.1
  refine ⟨t,ht,htJ.trans he,?_⟩
  change fixedCodim ρ J = 2
  rw [←he]
  exact hb.2.2.1

private theorem fixed_normalizer_of_image
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
      exact ⟨hx,fun j hj => congrArg M.subtype (hc ⟨j,hJM hj⟩ hj)⟩
    · rintro ⟨hx,hc⟩
      exact ⟨hx,fun j hj => Subtype.ext (hc j hj)⟩
  have hh := normalizes_fixed_of_image_normalizes f (V.subgroupOf M) (J.subgroupOf M)
    (X.subgroupOf M) le_normalizer_of_normal hker hn
  rw [he,←subgroupOf_normalizer_eq (inf_le_left.trans hV.le_selected)] at hh
  intro x hx
  exact hh (show (⟨x,hXM hx⟩ : M) ∈ X.subgroupOf M from hx)

/-- Every proper image of an original Sylow overgroup normalizes the original fixed subgroup. -/
theorem PreparedChosenModule.extraspecial_proper_image_normalizes_fixed
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V X : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hTX : (T : Subgroup G) ≤ X) (hXM : X ≤ M)
    (hne : (X.subgroupOf M).map (actionHom M V h.normalized).rangeRestrict ≠ ⊤) :
    X ≤ normalizer (thompsonFixed T V : Set G) := by
  let := h.elementary
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* internalActionImage M V h.normalized := (actionHom M V h.normalized).rangeRestrict
  let S := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V h.normalized).rangeRestrict_surjective
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let A := (X.subgroupOf M).map f
  obtain ⟨t,ht,htR,hcod⟩ := h.extraspecial_small_thompson_image hG T hempty hM hmany hJ hfull hex
  obtain ⟨_,_,_,hP,hPc,_,h6,hI⟩ := hex
  let : IsExtraspecial 3 (pResidual 2 (internalActionImage M V h.normalized)) := hP
  have hSR : (S : Subgroup D) ≤ normalizer (R : Set D) :=
    chosen_thompson_image_normalized _ _ _ hM.1.2 h.normalized
  have hSt : (S : Subgroup D) ≤ normalizer (zpowers t : Set D) := htR ▸ hSR
  have hSA : (S : Subgroup D) ≤ A := map_mono (subgroupOf_mono M hTX)
  have hn := SourceExtraspecialModel.proper_overgroup_normalizes_small_involution S hI ρ
    (imageRepresentation_injective M V h.normalized) hPc h6 t
    (ht ▸ pow_orderOf_eq_one t) (by rw [htR]; exact hcod.le) hSt A hSA hne
  rw [htR] at hn
  exact fixed_normalizer_of_image T hM.1.2 h hXM hn

/-- A third maximal intersection has action index nine and normalizes the
literal original Thompson fixed subgroup in the extraspecial row. -/
theorem PreparedChosenModule.extraspecial_third_intersection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    ¬ M ⊓ N ≤ Mc ∧
      (((M ⊓ N).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict).index = 9 ∧
      M ⊓ N ≤ normalizer (thompsonFixed T V : Set G) := by
  obtain ⟨hout,hn,hproper⟩ := h.third_maximal_action_constraints
    hG T hempty hM hJ hu hN hNM hNMc
  refine ⟨hout,?_,h.extraspecial_proper_image_normalizes_fixed hG T hempty hM hmany hJ hfull
    hex (le_inf hM.1.2 hN.2) inf_le_left hproper⟩
  let := h.elementary
  let f : M →* internalActionImage M V h.normalized := (actionHom M V h.normalized).rangeRestrict
  let S := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V h.normalized).rangeRestrict_surjective
  obtain ⟨_,_,_,hP,hPc,_,_,hI⟩ := hex
  let : IsExtraspecial 3 (pResidual 2 (internalActionImage M V h.normalized)) := hP
  exact SourceExtraspecialModel.proper_non_two_overgroup_index S hI hPc _
    (map_mono (subgroupOf_mono M (le_inf hM.1.2 hN.2))) hproper hn

private noncomputable def extraspecialFixedSpaceEquiv
    (M V A : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) (hAM : A ≤ M) :
    (V ⊓ centralizer (A : Set G) : Subgroup G) ≃
      fixedSpace (imageRepresentation M V hn)
        ((A.subgroupOf M).map (actionHom M V hn).rangeRestrict) where
  toFun v := ⟨Additive.ofMul ⟨v, v.property.1⟩, by
    rintro ⟨_, a, ha, rfl⟩
    apply congrArg Additive.ofMul
    apply Subtype.ext
    change (a : G) * (v : G) * (a : G)⁻¹ = v
    rw [v.property.2 a ha, mul_inv_cancel_right]⟩
  invFun v := ⟨v.val.toMul, v.val.toMul.property, by
    intro a ha
    have hv := v.property ⟨_, mem_map_of_mem (actionHom M V hn).rangeRestrict
      (show (⟨a, hAM ha⟩ : M) ∈ A.subgroupOf M from ha)⟩
    have he := congrArg (fun w : Additive V => (w.toMul : G)) hv
    change a * (v.val.toMul : G) * a⁻¹ = v.val.toMul at he
    exact mul_inv_eq_iff_eq_mul.mp he⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The original extraspecial Thompson fixed subgroup has order sixteen. -/
theorem PreparedChosenModule.extraspecial_thompson_fixed_card
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    Nat.card (thompsonFixed T V) = 16 := by
  let := h.elementary
  obtain ⟨t,_,htR,hcod⟩ := h.extraspecial_small_thompson_image hG T hempty hM hmany hJ hfull hex
  obtain ⟨_,_,_,_,_,_,h6,_⟩ := hex
  have hsum := fixedCodim_add_finrank (imageRepresentation M V h.normalized) (zpowers t)
  rw [htR,hcod,h6] at hsum
  have hd : Module.finrank (ZMod 2)
      (fixedSpace (imageRepresentation M V h.normalized)
        (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M V h.normalized).rangeRestrict)) = 4 := by
    exact Nat.add_left_cancel (hsum.trans (by decide : 6 = 2 + 4))
  rw [Nat.card_congr (extraspecialFixedSpaceEquiv M V (ChapterB.thompsonJ (T : Subgroup G) 1)
    h.normalized ((ChapterB.thompsonJ_le _ _).trans hM.1.2)),
    Module.natCard_eq_pow_finrank (K := ZMod 2),hd,Nat.card_zmod]
  norm_num

/-- The original intersection action has Sylow index three in the extraspecial row. -/
theorem PreparedChosenModule.extraspecial_third_action_relIndex
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict).relIndex
      (((M ⊓ N).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict) = 3 := by
  obtain ⟨_,hn,hproper⟩ := h.third_maximal_action_constraints
    hG T hempty hM hJ hu hN hNM hNMc
  let := h.elementary
  let f : M →* internalActionImage M V h.normalized := (actionHom M V h.normalized).rangeRestrict
  let S := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V h.normalized).rangeRestrict_surjective
  obtain ⟨_,_,_,hP,_,_,_,hI⟩ := hex
  let : IsExtraspecial 3 (pResidual 2 (internalActionImage M V h.normalized)) := hP
  exact SourceExtraspecialModel.proper_non_two_overgroup_relIndex S hI _
    (map_mono (subgroupOf_mono M (le_inf hM.1.2 hN.2))) hproper hn

end CFSG.Quasithin.Chapter15.Section01

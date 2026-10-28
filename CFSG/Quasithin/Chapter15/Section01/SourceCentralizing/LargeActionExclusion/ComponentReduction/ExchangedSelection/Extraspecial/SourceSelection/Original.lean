module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.SourceSelection
public import Theory.Representation.ExtraspecialBinarySix.CubicSelection
public import Theory.GroupTheory.PGroup.ExtraspecialResidualTwoRank
public import Theory.Representation.BinaryOffender.CubicConjugateDimension
/-!
# Original extraspecial image selection

The odd kernel of index two in the starred core makes every starred actor
cyclic. Its ratio is two, since the chosen quadratic ratio excludes one.
The original Thompson actors therefore have order two and fixed codimension
two; their nontrivial generated image also has order two. The faithful
extraspecial six-space supplies a noncentral cubic whose fixed plane is
fixed by this same involution. The stabilizer construction then supplies
all ImageMarking fields without a marking or fixed-plane hypothesis.

The parent Extraspecial module applies this marking to the actual component,
retaining the prime-three pre-exclusion witness and the four/sixteen planes.
Source: Aschbacher--Smith 15.1.13(4), 15.1.16(c)--18, pp.1091--1093.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
open Subgroup Representation Representation.BinaryOffender
open ChapterD ChapterD.UniqueFactor
open scoped ENNReal
universe u
variable {D W : Type u} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- The original extraspecial singleton has cubic ratio two. -/
theorem source_cubic_ratio (ρ : Representation (ZMod 2) D W)
    (hf : Function.Injective ρ) (hq : quadraticRatio ρ = 2) (S : Subgroup D)
    (hex : SourceCases.Extraspecial ρ S) : cubicRatio ρ = 2 := by
  obtain ⟨l,_⟩ := hex
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr
    ((cubicRatio_le_quadraticRatio ρ).trans_eq hq)
  have hAK : A ≤ Jhat ρ := le_sSup hA
  let := hA.1.2.1.2
  have hb := l.two_subgroup_inf_card_le_two (Jhat ρ) A (IsElementaryAbelian.isPGroup 2 A)
  rw [inf_eq_left.mpr hAK] at hb
  have hc : Nat.card A = 2 := by
    have hp := (one_lt_card_iff_ne_bot A).mpr hA.1.2.1.1
    omega
  have hr : rank A = 1 := by
    change Nat.log 2 (Nat.card A) = 1
    rw [hc]
    decide
  rcases QhatStar.ratio_one_or_two_of_rank_one ρ hf hA hr with h1 | h2
  · have hh := (isFFModule_iff_quadraticRatio_le_one ρ).mp
      ((isFFModule_iff_cubicRatio_le_one ρ).mpr h1.le)
    rw [hq] at hh
    norm_num at hh
  · exact h2
end CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
open ChapterD ChapterD.UniqueFactor Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Construct the noncentral cubic from the original Thompson marking. -/
theorem PreparedChosenModule.extraspecial_fixed_cubic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    letI := h.elementary
    ∃ X : Subgroup (pResidual 2 (internalActionImage M V h.normalized)),
      Nat.card X = 3 ∧ X ≠ center (pResidual 2 (internalActionImage M V h.normalized)) ∧
      fixedSpace (imageRepresentation M V h.normalized)
        (X.map (pResidual 2 (internalActionImage M V h.normalized)).subtype) ≤
      fixedSpace (imageRepresentation M V h.normalized)
        (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M V h.normalized).rangeRestrict) := by
  let := h.elementary
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f := (actionHom M V h.normalized).rangeRestrict
  let J := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  have hq := ExtraspecialMarker.source_cubic_ratio ρ (imageRepresentation_injective M V h.normalized)
    h.quadratic_ratio _ hex
  obtain ⟨l,_,_,hP,hcard,hexp,hdim,_⟩ := hex
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
  have he : (A.subgroupOf M).map f = J := eq_of_le_of_card_ge hBJ (by rw [hb.1,hjcard])
  obtain ⟨t,ht,htJ⟩ := CyclicSource.starred_generator ρ hb.2.2.2 hb.2.1
  have htJ' : zpowers t = J := htJ.trans he
  have hcod : fixedCodim ρ (zpowers t) ≤ 2 := by rw [htJ]; exact hb.2.2.1.le
  obtain ⟨X,hX,hXZ,hfix⟩ := ExtraspecialBinarySix.exists_noncentral_cubic_fixed_plane
    ρ (imageRepresentation_injective M V h.normalized) (pResidual 2 D) hcard hexp hdim t ht hcod
  refine ⟨X,hX,hXZ,?_⟩
  change fixedSpace ρ (X.map (pResidual 2 D).subtype) ≤ fixedSpace ρ J
  rwa [htJ'] at hfix

/-- All ImageMarking fields now follow from the original extraspecial action. -/
theorem PreparedChosenModule.extraspecial_imageMarking
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    letI := h.elementary; Nonempty (ExtraspecialMarker.ImageMarking T M V h.normalized) := by
  let := h.elementary
  obtain ⟨X,hX,hXZ,hfixed⟩ := h.extraspecial_fixed_cubic hG T hempty hM hmany hJ hfull hex
  obtain ⟨c,_⟩ := h.extraspecial_imageMarking_of_fixed_cubic hG T hempty hM hmany hJ
    hex X hX hXZ hfixed
  exact ⟨c⟩
end CFSG.Quasithin.Chapter15.Section01

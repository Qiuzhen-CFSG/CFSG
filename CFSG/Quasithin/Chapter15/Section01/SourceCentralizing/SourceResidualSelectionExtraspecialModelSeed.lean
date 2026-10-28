module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialModelSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialModelFixed
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialSquareRoot
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialAction

/-!
# Transport of the Sylow fixed-line bound to the original central seed

The full prepared module contains the original central involutions. Their
literal vectors inject into the fixed space of the actual Sylow action.
A one-dimensional fixed-space bound therefore gives order two for that
same ambient seed. In the extraspecial row, a third maximal local supplies
center movement, while the intrinsic square-root theorem supplies that bound.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

namespace SourceExtraspecialModel
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- The entire Sylow fixed space lies in the plane moved by the small
involution in the extraspecial residual action. -/
theorem residual_sylow_fixed_le_moved
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥) [IsExtraspecial 3 (pResidual 2 D)]
    (hP : Nat.card (pResidual 2 D) = 27)
    (hexp : Monoid.exponent (pResidual 2 D) = 3)
    (h6 : Module.finrank (ZMod 2) W = 6) (S : Sylow 2 D)
    (hI : ChapterD.Section03.FrattiniIrreducible (S : Subgroup D)
      (pResidual 2 D) le_normalizer_of_normal)
    (t : D) (htS : t ∈ (S : Subgroup D)) (ht : orderOf t = 2)
    (hr : fixedCodim ρ (zpowers t) = 2) :
    fixedSpace ρ (S : Subgroup D) ≤ subspaceCommutator ρ ⊤ (zpowers t) ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (zpowers t)) = 2 := by
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htC := ExtraspecialBinarySix.small_involution_centralizes_center ρ hf
    (pResidual 2 D) hP h6 t ht2 hr.le
  obtain ⟨x,hxS,_,hxt,hxc⟩ :=
    residual_sylow_square_root_of_center_fixing_involution hcore hP hexp S hI t htS ht htC
  obtain ⟨he,hd⟩ := extraspecial_square_root_fixed_plane ρ hf
    (pResidual 2 D) hP h6 x t ht2 hxt hxc hr
  exact ⟨he ▸ fixedSpace_antitone ρ (zpowers_le.mpr hxS),he ▸ hd⟩

end SourceExtraspecialModel

/-- A fixed-line bound in the original full action gives order two for
the original central-involution seed. -/
theorem PreparedChosenModule.full_seed_card_two_of_sylow_fixed_dimension
    (T : Sylow 2 G) {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hd : letI := h.elementary
      Module.finrank (ZMod 2) (fixedSpace (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) ≤ 1) :
    Nat.card (centralInvolutions T) = 2 := by
  let := h.elementary
  have hZV : centralInvolutions T ≤ V := by rw [hfull]; exact le_conjugateSpanBy _ _
  let ρ := imageRepresentation M V h.normalized
  let f : M →* internalActionImage M V h.normalized := (actionHom M V h.normalized).rangeRestrict
  let S := ((T : Subgroup G).subgroupOf M).map f
  let j : centralInvolutions T → fixedSpace ρ S := fun z =>
    ⟨Additive.ofMul ⟨z,hZV z.property⟩,by
      rintro ⟨_,t,ht,rfl⟩
      apply congrArg Additive.ofMul
      apply Subtype.ext
      change (t : G)*(z : G)*(t : G)⁻¹=z
      rw [centralInvolutions_le_centralizer_sylow T z.property t ht,mul_inv_cancel_right]⟩
  have hj : Function.Injective j := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun v : fixedSpace ρ S => (v.val.toMul : G)) he
  have hc : Nat.card (centralInvolutions T) ≤ 2 := by
    apply (Nat.card_le_card_of_injective j hj).trans
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hd).trans_eq (by decide)
  have hn := (centralInvolutions T).one_lt_card_iff_ne_bot.mpr
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  omega

/-- A third maximal local forces the original Sylow fixed space to have
at most one binary dimension. -/
theorem PreparedChosenModule.extraspecial_third_sylow_fixed_dimension_le_one
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
    letI := h.elementary
    Module.finrank (ZMod 2) (fixedSpace (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) ≤ 1 := by
  let := h.elementary
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  let S := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V h.normalized).rangeRestrict_surjective
  obtain ⟨t,ht,htR,hr⟩ := h.extraspecial_small_thompson_image
    hG T hempty hM hmany hJ hfull hex
  have htS : t ∈ (S : Subgroup D) := by
    apply (map_mono (subgroupOf_mono M (ChapterB.thompsonJ_le _ 1)))
    exact htR ▸ mem_zpowers t
  have hm := h.extraspecial_third_sylow_moves_center
    hG T hempty hM hJ hu hfull hex hN hNM hNMc
  obtain ⟨_,_,_,hP,hPc,hexp,h6,hI⟩ := hex
  let : IsExtraspecial 3 (pResidual 2 D) := hP
  have hcore : pCore 2 D = ⊥ := by
    subst V
    exact source_localAction_twoCore hG T hM
  exact SourceExtraspecialModel.residual_sylow_fixed_dimension_le_one ρ
    (imageRepresentation_injective M V h.normalized) hcore hPc hexp h6 S hI t htS ht
    (by rwa [htR]) hm

/-- The original central involution seed has order two whenever the
extraspecial row admits a third maximal local. -/
theorem PreparedChosenModule.extraspecial_third_seed_card_two
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
    Nat.card (centralInvolutions T) = 2 :=
  h.full_seed_card_two_of_sylow_fixed_dimension T hM hfull
    (h.extraspecial_third_sylow_fixed_dimension_le_one
      hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc)

/-- In the original full extraspecial action, the literal central seed
lies in the two-dimensional space moved by the Thompson image. -/
theorem PreparedChosenModule.extraspecial_seed_le_thompson_moved
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
    AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup ≤
      subspaceCommutator ρ ⊤ R ∧
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ R) = 2 := by
  let := h.elementary
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  let S := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V h.normalized).rangeRestrict_surjective
  obtain ⟨t,ht,htR,hr⟩ := h.extraspecial_small_thompson_image
    hG T hempty hM hmany hJ hfull hex
  have htS : t ∈ (S : Subgroup D) := by
    apply (map_mono (subgroupOf_mono M (ChapterB.thompsonJ_le _ 1)))
    exact htR ▸ mem_zpowers t
  obtain ⟨_,_,_,hP,hPc,hexp,h6,hI⟩ := hex
  let : IsExtraspecial 3 (pResidual 2 D) := hP
  have hcore : pCore 2 D = ⊥ := by
    subst V
    exact source_localAction_twoCore hG T hM
  have hp := SourceExtraspecialModel.residual_sylow_fixed_le_moved ρ
    (imageRepresentation_injective M V h.normalized) hcore hPc hexp h6 S hI t htS ht
    (by rwa [htR])
  rw [htR] at hp
  refine ⟨le_trans ?_ hp.1,hp.2⟩
  intro v hv
  rintro ⟨_,a,ha,rfl⟩
  change (v.toMul : G) ∈ centralInvolutions T at hv
  apply congrArg Additive.ofMul
  apply Subtype.ext
  change (a : G) * (v.toMul : G) * (a : G)⁻¹ = v.toMul
  rw [centralInvolutions_le_centralizer_sylow T hv a ha,mul_inv_cancel_right]

end CFSG.Quasithin.Chapter15.Section01

module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelCoreLinear

/-!
# Original kernel-core displacement in the moved plane

The central cubic preimage normalizes the moved plane, hence lies in the
literal partner. It therefore normalizes the partner's two-core. The
two-core image centralizes the cubic by coprime mutual normalization.
Its action on the binary plane section E/U is consequently trivial.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Section02.ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

set_option backward.isDefEq.respectTransparency false in
/-- The actual moved-plane centralizer's two-core moves the original
Thompson fixed subgroup only within the original moved plane. -/
theorem PreparedChosenModule.extraspecial_moved_centralizer_core_displacement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    ⁅(centralizer (U : Set G)).pCoreIn 2,thompsonFixed T V⁆ ≤ U := by
  let := h.elementary
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let Q := Mc.pCoreIn 2
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  have hf : Function.Surjective f := (actionHom M V h.normalized).rangeRestrict_surjective
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let P := pResidual 2 D
  let ZP := (center P).map P.subtype
  let B := (Q.subgroupOf M).map f
  let WU := subspaceCommutator ρ ⊤ R
  let WE := fixedSpace ρ R
  have hcore := h.extraspecial_moved_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  change (centralizer (U : Set G)).pCoreIn 2 = Q ∧ _ at hcore
  change ⁅(centralizer (U : Set G)).pCoreIn 2,thompsonFixed T V⁆ ≤ U
  rw [hcore.1]
  have hQT : Q ≤ (T : Subgroup G) := hcore.1 ▸ hcore.2.1
  have hQM : Q ≤ M := hQT.trans hM.1.2
  have hQnorm : Mc ≤ normalizer (Q : Set G) :=
    Mc.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  have hmod := h.extraspecial_partner_module_and_normalizer
    hG T hempty hM hmany hJ hu hfull hex
  obtain ⟨t,ht,htR,hr⟩ := h.extraspecial_small_thompson_image
    hG T hempty hM hmany hJ hfull hex
  change zpowers t = R at htR
  change fixedCodim ρ R = 2 at hr
  obtain ⟨_,_,_,hP,hPc,_,h6,_⟩ := hex
  let : IsExtraspecial 3 P := hP
  have hZc : Nat.card ZP = 3 := by
    rw [card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P]
  have hZfix := SourceExtraspecialModel.extraspecial_center_fixedSpace_eq_bot ρ
    (imageRepresentation_injective M V h.normalized) P hPc h6
  have htZ : t ∈ centralizer (ZP : Set D) :=
    ExtraspecialBinarySix.small_involution_centralizes_center ρ
      (imageRepresentation_injective M V h.normalized) P hPc h6 t
      (ht ▸ pow_orderOf_eq_one t) (by rw [htR]; exact hr.le)
  have hZR : ZP ≤ normalizer (R : Set D) := by
    rw [←htR]
    exact (le_centralizer_iff.mp (zpowers_le.mpr htZ)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hZstable : ZP ≤ subspaceStabilizer ρ WU :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hZR
  have hJM := (ChapterB.thompsonJ_le (T : Subgroup G) 1).trans hM.1.2
  have hUambient := ambientSpace_moved h.normalized h.le_selected hJM
  change ambientSpace V WU = U at hUambient
  have hEambient := ambientSpace_fixed h.normalized hJM
  change ambientSpace V WE = thompsonFixed T V at hEambient
  have hZpre : (ZP.comap f).map M.subtype ≤ Mc := by
    rw [hmod.2]
    change (ZP.comap f).map M.subtype ≤ normalizer (U : Set G)
    rw [←hUambient]
    apply le_normalizer_iff.mpr
    rintro _ ⟨m,hm,rfl⟩ _ ⟨v,hv,rfl⟩
    exact ⟨(ρ (f m) (Additive.ofMul v)).toMul,
      (hZstable hm (Additive.ofMul v)).2 hv,rfl⟩
  have hZB : ZP ≤ normalizer (B : Set D) := by
    intro z hz
    obtain ⟨m,hm⟩ := hf z
    have hmMc : (m : G) ∈ Mc := hZpre ⟨m,show f m ∈ ZP from hm.symm ▸ hz,rfl⟩
    have hmQ : m ∈ normalizer (Q.subgroupOf M : Set M) := by
      rw [←subgroupOf_normalizer_eq hQM]
      exact hQnorm hmMc
    exact hm ▸ (Q.subgroupOf M).le_normalizer_map f (mem_map_of_mem f hmQ)
  have hBZ : B ≤ normalizer (ZP : Set D) := by
    exact le_normalizer_of_normal
  have hB2 : IsPGroup 2 B := (isPGroup_pCoreIn 2 Mc).comap_subtype.map f
  have hZ3 : IsPGroup 3 ZP := IsPGroup.of_card (n := 1) hZc
  have hBC : B ≤ centralizer (ZP : Set D) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp hZB)
      (le_normalizer_iff_commutator_le_right.mp hBZ)).trans
        (hB2.disjoint_of_coprime hZ3 (by decide)).le_bot
  have hBR : B ≤ normalizer (R : Set D) :=
    (map_mono (subgroupOf_mono M hQT)).trans
      (chosen_thompson_image_normalized T M V hM.1.2 h.normalized)
  have hUE : WU ≤ WE := by
    have hquad : IsQuadratic ρ R := by
      rw [←htR]
      exact (involution_actor_rank_and_fixedCodim ρ t ht).2.2.1
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩ b
    exact hquad b b.property a ha v
  have hUdim : Module.finrank (ZMod 2) WU = 2 := by
    change Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ R) = 2
    rw [←htR,CyclicFixedRank.commutator_eq_range]
    exact (fixedCodim_zpowers_eq_displacement_rank ρ t).symm.trans (htR ▸ hr)
  have hdim : Module.finrank (ZMod 2) WE = Module.finrank (ZMod 2) WU + 2 := by
    have hh := fixedCodim_add_finrank ρ R
    rw [hr,h6] at hh
    change _ + Module.finrank (ZMod 2) WE = _ at hh
    omega
  apply commutator_le.mpr
  intro q hq e he
  let qM : M := ⟨q,hQM hq⟩
  have hqB : f qM ∈ B := mem_map_of_mem f hq
  have heV : e ∈ V := he.1
  let v : V := ⟨e,heV⟩
  have hv : Additive.ofMul v ∈ WE := (mem_ambientSpace _ v).mp (hEambient.symm ▸ he)
  have hdisp := SourceExtraspecialModel.two_element_fixed_displacement ρ R ZP hZc hZR hZfix
    hUE hdim (f qM) (by
      obtain ⟨n,hn⟩ := hB2 ⟨f qM,hqB⟩
      exact ⟨n,congrArg Subtype.val hn⟩) (hBR hqB) (hBC hqB) (Additive.ofMul v) hv
  rw [←hUambient]
  refine ⟨(ρ (f qM) (Additive.ofMul v) - Additive.ofMul v).toMul,hdisp,?_⟩
  simp only [toMul_sub,div_eq_mul_inv]
  change q * e * q⁻¹ * e⁻¹ = ⁅q,e⁆
  simp only [commutatorElement_def,mul_assoc]

end CFSG.Quasithin.Chapter15.Section01

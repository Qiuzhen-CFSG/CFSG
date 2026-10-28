module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelCoreDisplacement

/-!
# The full module's displacement under the original kernel core

The core centralizes U and its image normalizes the order-two Thompson
actor, hence commutes with that actor. Commuting the two linear differences
therefore puts every core displacement of V in E=C_V(J₁(T)).
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Section02.ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

set_option backward.isDefEq.respectTransparency false in
/-- The same original core sends the full module into the original fixed
subgroup under commutation. -/
theorem PreparedChosenModule.extraspecial_moved_centralizer_full_displacement
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
    ⁅(centralizer (U : Set G)).pCoreIn 2,V⁆ ≤ thompsonFixed T V := by
  let := h.elementary
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let Q := (centralizer (U : Set G)).pCoreIn 2
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let WU := subspaceCommutator ρ ⊤ R
  let WE := fixedSpace ρ R
  have hcore := h.extraspecial_moved_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  have hQT : Q ≤ (T : Subgroup G) := hcore.2.1
  have hQM : Q ≤ M := hQT.trans hM.1.2
  have hQU : Q ≤ centralizer (U : Set G) := pCoreIn_le 2 _
  obtain ⟨t,ht,htR,_⟩ := h.extraspecial_small_thompson_image
    hG T hempty hM hmany hJ hfull hex
  change zpowers t = R at htR
  have hRc : Nat.card R = 2 := by rw [←htR,Nat.card_zpowers,ht]
  have hQR : (Q.subgroupOf M).map f ≤ centralizer (R : Set D) :=
    ((map_mono (subgroupOf_mono M hQT)).trans
      (chosen_thompson_image_normalized T M V hM.1.2 h.normalized)).trans
        (normalizer_le_centralizer_of_card_two R hRc)
  have hJM := (ChapterB.thompsonJ_le (T : Subgroup G) 1).trans hM.1.2
  have hUambient := ambientSpace_moved h.normalized h.le_selected hJM
  change ambientSpace V WU = U at hUambient
  have hEambient := ambientSpace_fixed h.normalized hJM
  change ambientSpace V WE = thompsonFixed T V at hEambient
  change ⁅Q,V⁆ ≤ thompsonFixed T V
  apply commutator_le.mpr
  intro q hq v hv
  let qM : M := ⟨q,hQM hq⟩
  let w : Additive V := Additive.ofMul ⟨v,hv⟩
  have hqR : f qM ∈ centralizer (R : Set D) := hQR (mem_map_of_mem f hq)
  have hqfix : ∀ u ∈ WU, ρ (f qM) u = u := by
    intro u hu
    have huU : (u.toMul : G) ∈ U := hUambient ▸ ⟨u.toMul,hu,rfl⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change q * (u.toMul : G) * q⁻¹ = u.toMul
    rw [←hQU hq u.toMul huU,mul_inv_cancel_right]
  have hdisp : ρ (f qM) w - w ∈ WE := by
    intro a
    change ρ (a : D) (ρ (f qM) w - w) = ρ (f qM) w - w
    rw [map_sub]
    have hc : ρ (a : D) (ρ (f qM) w) = ρ (f qM) (ρ (a : D) w) := by
      rw [←Module.End.mul_apply,←map_mul,hqR a a.property,map_mul,Module.End.mul_apply]
    rw [hc]
    have hh := hqfix (ρ (a : D) w - w)
      (Submodule.subset_span ⟨a,a.property,w,Submodule.mem_top,rfl⟩)
    rw [map_sub] at hh
    calc
      ρ (f qM) (ρ (a : D) w) - ρ (a : D) w =
          (ρ (f qM) (ρ (a : D) w) - ρ (f qM) w) -
            (ρ (a : D) w - w) + (ρ (f qM) w - w) := by abel
      _ = ρ (f qM) w - w := by rw [hh,sub_self,zero_add]
  rw [←hEambient]
  refine ⟨(ρ (f qM) w - w).toMul,hdisp,?_⟩
  simp only [toMul_sub,div_eq_mul_inv]
  change q * v * q⁻¹ * v⁻¹ = ⁅q,v⁆
  simp only [commutatorElement_def,mul_assoc]

end CFSG.Quasithin.Chapter15.Section01

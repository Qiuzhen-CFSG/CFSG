module
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The point radical and cubic quotient fixers in SL₃(4)

The actual point-local two-core has additive plane coordinates and order q².
Over the four-element field, a cubic element preserving the first coordinate
line and centralizing the point-local core quotient must be scalar in SL₃.
The two elementary matrices in the lower 2×2 block first force a scalar
linear part; determinant one and the cubic equation remove the remaining
upper-right entries.

These intrinsic calculations retain the full SL₃ group and the actual
point-local radical. In particular a central cubic cannot move that radical.
They diagnose the scope of the torus movement step in Aschbacher--Smith,
original 4.3.2, printed pp.617--619; the local coordinates are those of
F.1.12(I)(1), printed pp.262--264.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups commutatorElement
namespace Matrix.PSL3.LinearThree
variable {F : Type*} [Field F]

private theorem bottom_mul_eq_of_commutator_radical
    (a b : SL(3,F)) (hc : ⁅a,b⁆ ∈ (pointRadicalSL F).map (pointLocalSL F).subtype)
    (i : Fin 3) (hi : i = 1 ∨ i = 2) (j : Fin 3) :
    (a * b).val i j = (b * a).val i j := by
  obtain ⟨w,hw,he⟩ := hc
  obtain ⟨h11,h12,h21,h22⟩ := (mem_pointRadicalSL_iff F w).mp hw
  obtain ⟨_,h10,h20⟩ := (mem_pointLocalSL_iff F w).mp w.property
  have hm : (w : SL(3,F)) * (b * a) = a * b := by
    change (w : SL(3,F)) = ⁅a,b⁆ at he
    rw [he]
    simp only [commutatorElement_def,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one]
  have hh := congrArg (fun g : SL(3,F) => g.val i j) hm
  rcases hi with rfl | rfl <;>
    simpa only [SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_three,
      h11,h12,h21,h22,h10,h20,zero_mul,one_mul,zero_add,add_zero] using hh.symm

/-- Over F₄, a cubic root-normalizer element central on the point-local
core quotient is already central in SL₃. -/
theorem cubic_pointParabolic_central_of_core_action [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (a : SL(3,F))
    (ha : a ∈ pointParabolicSL F) (ha3 : a ^ 3 = 1)
    (hc : ∀ b ∈ pointLocalSL F,
      ⁅a,b⁆ ∈ (pointRadicalSL F).map (pointLocalSL F).subtype) :
    a ∈ center SL(3,F) := by
  obtain ⟨h10,h20⟩ := (mem_pointParabolicSL_iff F a).mp ha
  let u := SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) (1 : F)
  let v := SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) (1 : F)
  have hu : u ∈ pointLocalSL F := by
    rw [mem_pointLocalSL_iff]; simp [u,SpecialLinearGroup.transvection_coe]
  have hv : v ∈ pointLocalSL F := by
    rw [mem_pointLocalSL_iff]; simp [v,SpecialLinearGroup.transvection_coe]
  have h21 : a.val 2 1 = 0 := by
    have hh := bottom_mul_eq_of_commutator_radical a u (hc u hu) 1 (Or.inl rfl) 1
    simpa [u,SpecialLinearGroup.transvection_coe,SpecialLinearGroup.coe_mul,
      Matrix.mul_apply,Fin.sum_univ_three] using hh.symm
  have h12 : a.val 1 2 = 0 := by
    have hh := bottom_mul_eq_of_commutator_radical a v (hc v hv) 2 (Or.inr rfl) 2
    simpa [v,SpecialLinearGroup.transvection_coe,SpecialLinearGroup.coe_mul,
      Matrix.mul_apply,Fin.sum_univ_three] using hh.symm
  have hdiag : a.val 1 1 = a.val 2 2 := by
    have hh := bottom_mul_eq_of_commutator_radical a u (hc u hu) 1 (Or.inl rfl) 2
    simpa [u,SpecialLinearGroup.transvection_coe,SpecialLinearGroup.coe_mul,
      Matrix.mul_apply,Fin.sum_univ_three,h12] using hh
  let t := a.val 2 2
  have hdet : a.val 0 0 * t ^ 2 = 1 := by
    have hh := a.property
    rw [Matrix.det_fin_three] at hh
    simpa [Matrix.det_fin_three,h10,h20,h12,h21,hdiag,t,pow_two,mul_assoc] using hh
  have ht : t ≠ 0 := by intro hz; simp [hz] at hdet
  have ht3 : t ^ 3 = 1 := by
    let := Fintype.ofFinite F
    have hh := FiniteField.pow_card_sub_one_eq_one t ht
    rw [←Nat.card_eq_fintype_card,hF] at hh
    exact hh
  have h00 : a.val 0 0 = t := by
    apply mul_right_cancel₀ (pow_ne_zero 2 ht)
    rw [hdet,←pow_succ',ht3]
  have h01 : a.val 0 1 = 0 := by
    have hh := congrArg (fun g : SL(3,F) => g.val 0 1) ha3
    have hh' : t ^ 2 * a.val 0 1 = 0 := by
      simpa [pow_succ,SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_three,
        h10,h20,h12,h21,hdiag,h00,t,CharTwo.add_self_eq_zero,mul_assoc,mul_comm,mul_left_comm]
        using hh
    exact (mul_eq_zero.mp hh').resolve_left (pow_ne_zero 2 ht)
  have h02 : a.val 0 2 = 0 := by
    have hh := congrArg (fun g : SL(3,F) => g.val 0 2) ha3
    have hh' : t ^ 2 * a.val 0 2 = 0 := by
      simpa [pow_succ,SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_three,
        h10,h20,h12,h21,hdiag,h00,h01,t,CharTwo.add_self_eq_zero,mul_assoc,mul_comm,mul_left_comm]
        using hh
    exact (mul_eq_zero.mp hh').resolve_left (pow_ne_zero 2 ht)
  apply SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨t,by simpa using ht3,?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10,h20,h12,h21,hdiag,h00,h01,h02,t]
end Matrix.PSL3.LinearThree

namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
noncomputable def pointLocalSLTwoCoreEquiv :
    pCore 2 (pointLocalSL F) ≃* Multiplicative (Fin 2 → F) :=
  ((pCore 2 (pointLocalSL F)).equivMapOfInjective
    (pointLocalAffineEquiv F).toMonoidHom (pointLocalAffineEquiv F).injective).trans
    ((MulEquiv.subgroupCongr ((pCore_map_iso 2 (pointLocalAffineEquiv F)).trans
      (Matrix.SL2.affine_twoCore_eq F))).trans (Matrix.SL2.translationsEquiv F).symm)

theorem card_pointLocalSL_twoCore : Nat.card (pCore 2 (pointLocalSL F)) = Nat.card F ^ 2 := by
  rw [Nat.card_congr (pointLocalSLTwoCoreEquiv F).toEquiv]
  change Nat.card (Fin 2 → F) = _
  rw [Nat.card_fun,Nat.card_fin]
end Matrix.PSL3.LinearThree

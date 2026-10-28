module
public import Theory.SpecificGroups.PSL3.LinearThreeRadicalCubic

/-!
# Fixed points on the point radical over F₃₂

An element preserving the first coordinate line and centralizing the point
local modulo its two-core has scalar lower block. If its root action is
nontrivial, the two diagonal weights differ: F₃₂ has no nontrivial cube root
of unity. Commutation therefore forces both coordinates of a fixed radical
element to vanish.

This is the degree-five root-plane calculation used in the J₄ branch of
Aschbacher--Smith 4.3.16, printed pp.617--618. It keeps the actual SL₃
parabolic and radical and does not extend the movement assertion to F₄.
-/

public section
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

/-- A nontrivial root action has no fixed point on the actual radical over F₃₂. -/
theorem pointParabolic_radical_fixed_eq_one_thirtyTwo [Finite F] [CharP F 2]
    (hF : Nat.card F = 32) (a : SL(3,F))
    (ha : a ∈ pointParabolicSL F) (hroot : a.val 0 0 ≠ 1)
    (hc : ∀ b ∈ pointLocalSL F,
      ⁅a,b⁆ ∈ (pointRadicalSL F).map (pointLocalSL F).subtype)
    (b : pointLocalSL F) (hb : b ∈ pointRadicalSL F)
    (hab : a * (b : SL(3,F)) = b * a) : b = 1 := by
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
  have hne : a.val 0 0 ≠ t := by
    intro he
    have ht3 : t^3 = 1 := by simpa only [he, ←pow_succ'] using hdet
    let := Fintype.ofFinite F
    have ht31 := FiniteField.pow_card_sub_one_eq_one t ht
    rw [←Nat.card_eq_fintype_card,hF] at ht31
    have ht1 : t=1 := by
      have hp : t^31=t := by
        calc
          t^31 = (t^3)^10*t := by ring
          _ = t := by rw [ht3,one_pow,one_mul]
      exact hp.symm.trans ht31
    exact hroot (he.trans ht1)
  obtain ⟨b00,b10,b20⟩ := (mem_pointLocalSL_iff F b).mp b.property
  obtain ⟨b11,b12,b21,b22⟩ := (mem_pointRadicalSL_iff F b).mp hb
  have b01 : b.val.val 0 1 = 0 := by
    have hh := congrArg (fun g : SL(3,F) => g.val 0 1) hab
    have hh' : a.val 0 0 * b.val.val 0 1 = t * b.val.val 0 1 := by
      simp only [SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_three,
        b00,b11,b21,hdiag,h21,mul_zero,one_mul,mul_one,add_zero] at hh
      dsimp only [t]
      linear_combination hh
    exact (mul_eq_mul_right_iff.mp hh').resolve_left hne
  have b02 : b.val.val 0 2 = 0 := by
    have hh := congrArg (fun g : SL(3,F) => g.val 0 2) hab
    have hh' : a.val 0 0 * b.val.val 0 2 = t * b.val.val 0 2 := by
      simp only [SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_three,
        b00,b12,b22,h12,mul_zero,one_mul,mul_one,add_zero] at hh
      dsimp only [t]
      linear_combination hh
    exact (mul_eq_mul_right_iff.mp hh').resolve_left hne
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [b00,b01,b02,b10,b11,b12,b20,b21,b22]
end Matrix.PSL3.LinearThree

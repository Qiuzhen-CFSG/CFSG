module
public import Theory.Representation.SL2SylowFixedRecognition.Definitions
public import Mathlib.LinearAlgebra.Projection

/-!
# Root matrices for binary SL₂ recognition

The upper root group and the Weyl involution generate SL₂. The standard
six-factor diagonal word supplies the field multiplication identities used
in the coordinate proof of G.1.7 (Aschbacher--Smith, pp.329--330).
-/
@[expose] public noncomputable section
open Matrix Subgroup
open scoped MatrixGroups
namespace Representation.SL2SylowFixedRecognition
namespace RootCoordinates
variable {F : Type*} [Field F] [CharP F 2]

def upper (t : F) : SL(2,F) := SpecialLinearGroup.transvection zero_ne_one t

def weyl : SL(2,F) := ⟨!![0,1;1,0], by simp [det_fin_two,CharTwo.neg_eq]⟩

omit [CharP F 2] in
theorem upper_val (t : F) : (upper t).val = !![1,t;0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper,SpecialLinearGroup.transvection_coe]

theorem weyl_mul_self : (weyl : SL(2,F)) * weyl = 1 := by
  apply Subtype.ext
  change (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) F) * !![0,1;1,0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply,Fin.sum_univ_two]

theorem weyl_inv : (weyl : SL(2,F))⁻¹ = weyl := inv_eq_of_mul_eq_one_right weyl_mul_self

omit [CharP F 2] in
theorem upper_zero : upper (0 : F) = 1 := SpecialLinearGroup.transvection_coeff_zero _

omit [CharP F 2] in
theorem upper_add (t s : F) : upper (t+s) = upper t * upper s :=
  SpecialLinearGroup.transvection_add _ t s

theorem upper_one_braid : upper (1 : F) * weyl * upper 1 = weyl * upper 1 * weyl := by
  apply Subtype.ext
  change (upper (1 : F)).val * weyl.val * (upper 1).val =
    weyl.val * (upper 1).val * weyl.val
  rw [upper_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl,mul_apply,Fin.sum_univ_two,CharTwo.add_self_eq_zero]

theorem weyl_upper_weyl (t : F) :
    weyl * upper t * weyl = SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero t := by
  apply Subtype.ext
  change weyl.val * (upper t).val * weyl.val = _
  rw [upper_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl,mul_apply,Fin.sum_univ_two,SpecialLinearGroup.transvection_coe]

theorem upper_weyl_induction (P : SL(2,F) → Prop)
    (hu : ∀ t, P (upper t)) (hw : P weyl)
    (hm : ∀ a b, P a → P b → P (a*b)) (g : SL(2,F)) : P g := by
  apply Matrix.SL2.transvection_induction P ?_ hm g
  intro i j hij t
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact hu t
  · rw [← weyl_upper_weyl]
    exact hm _ _ (hm _ _ hw (hu t)) hw
  · exact (hij rfl).elim

def diagonalWord (a : F) : SL(2,F) :=
  upper a * weyl * upper a⁻¹ * weyl * upper a * weyl

theorem diagonalWord_val {a : F} (ha : a ≠ 0) :
    (diagonalWord a).val = !![a,0;0,a⁻¹] := by
  change (upper a).val * weyl.val * (upper a⁻¹).val * weyl.val * (upper a).val *
    weyl.val = _
  rw [upper_val,upper_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl,mul_apply,Fin.sum_univ_two,ha,CharTwo.add_self_eq_zero]

theorem diagonalWord_upper {a : F} (ha : a ≠ 0) (b : F) :
    diagonalWord a * upper b = upper (a*a*b) * diagonalWord a := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalWord_val ha,upper_val,
      mul_apply,Fin.sum_univ_two,ha,mul_assoc]
  field_simp

end RootCoordinates
end Representation.SL2SylowFixedRecognition

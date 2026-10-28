module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.FinCases

/-!
# An involution in the derived group of Sp₄ in characteristic two

Use the upper transvection on the first hyperbolic pair and the isometry
swapping the two hyperbolic pairs. Their commutator has block matrix
`[I I; 0 I]`, a nonidentity involution in characteristic two. The calculation
also works over the field of two elements, where Sp₄ itself is not perfect.
All matrices belong to Mathlib's actual symplectic group; its carrier is the
one used by the Atlas symplectic model.

Source: the classical matrix models in Aschbacher--Smith,
*The Classification of Quasithin Groups*, E.1.14(1).
-/

public section

open Matrix
open scoped Matrix commutatorElement
namespace Theory.SpecificGroups.SymplecticFour

variable {F : Type*} [Field F]

private def upper : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks 1 !![1, 0; 0, 0] 0 1

private def switch : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, 0]

private def swap : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks switch 0 0 switch

private theorem switch_sq : (switch : Matrix (Fin 2) (Fin 2) F) * switch = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [switch, Matrix.mul_apply, Fin.sum_univ_two]

private theorem switch_transpose : (switch : Matrix (Fin 2) (Fin 2) F)ᵀ = switch := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem upper_mem : upper (F := F) ∈ symplecticGroup (Fin 2) F := by
  rw [SymplecticGroup.mem_iff]
  simp only [upper, Matrix.J, fromBlocks_multiply, fromBlocks_transpose,
    transpose_one, transpose_zero, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, zero_add, add_zero, mul_neg, neg_mul, neg_zero]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem swap_mem : swap (F := F) ∈ symplecticGroup (Fin 2) F := by
  rw [SymplecticGroup.mem_iff]
  simp [swap, Matrix.J, fromBlocks_multiply, fromBlocks_transpose,
    switch_transpose, switch_sq]

variable [CharP F 2]

private theorem matrix_add_self (A : Matrix (Fin 2) (Fin 2) F) : A + A = 0 := by
  ext i j
  simp [CharTwo.add_self_eq_zero]

/-- A genuine involution in Sp₄(F)', including the exceptional binary case. -/
theorem exists_involution_derived_of_char_two :
    ∃ x : commutator (symplecticGroup (Fin 2) F), x ≠ 1 ∧ x ^ 2 = 1 := by
  let u : symplecticGroup (Fin 2) F := ⟨upper, upper_mem⟩
  let w : symplecticGroup (Fin 2) F := ⟨swap, swap_mem⟩
  have hu : u * u = 1 := by
    apply Subtype.ext
    change upper * upper = (1 : Matrix _ _ F)
    simp only [upper, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.mul_one, Matrix.one_mul, zero_add, add_zero, matrix_add_self, fromBlocks_one]
  have hw : w * w = 1 := by
    apply Subtype.ext
    change swap * swap = (1 : Matrix _ _ F)
    simp [swap, fromBlocks_multiply, switch_sq]
  have he : ⁅w, u⁆ = w * u * w * u := by
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_left hw, inv_eq_of_mul_eq_one_left hu]
  have hz : (⁅w, u⁆ : symplecticGroup (Fin 2) F).val = fromBlocks 1 1 0 1 := by
    rw [he]
    change swap * upper * swap * upper = (fromBlocks 1 1 0 1 : Matrix _ _ F)
    simp only [swap, upper, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.mul_one, Matrix.one_mul, zero_add, add_zero, switch_sq]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [switch]
  refine ⟨⟨⁅w, u⁆, Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _)⟩, ?_, ?_⟩
  · intro h
    have hh : ⁅w, u⁆ = 1 := congrArg Subtype.val h
    have ha := congrArg (fun a : symplecticGroup (Fin 2) F => a.val (.inl 0) (.inr 0)) hh
    rw [hz] at ha
    simp at ha
  · apply Subtype.ext
    change ⁅w, u⁆ ^ 2 = 1
    apply Subtype.ext
    change (⁅w, u⁆ : symplecticGroup (Fin 2) F).val ^ 2 = (1 : Matrix _ _ F)
    rw [hz, pow_two]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.mul_one,
      zero_add, add_zero, matrix_add_self, fromBlocks_one]

end Theory.SpecificGroups.SymplecticFour

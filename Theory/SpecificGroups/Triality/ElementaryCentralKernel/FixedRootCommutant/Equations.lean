module
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRootCommutant.Supports

/-! Entry equations for the four constant fixed roots, using their checked
sparse row and column supports. -/

public section
namespace Triality.Standard.ElementaryCentralKernel.FixedRootCommutant

variable {F : Type*} [CommRing F]

private lemma mul_constant_entry (A : Matrix (Fin 28) (Fin 28) F)
    (k : Fin 4) (r c : Fin 28) :
    (A * constantMatrix (F := F) k) r c = ∑ j ∈ constantCols k c, A r j := by
  simp only [Matrix.mul_apply, constantMatrix, supportMatrix, constantCols_check,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_mem_eq]

private lemma constant_mul_entry (A : Matrix (Fin 28) (Fin 28) F)
    (k : Fin 4) (r c : Fin 28) :
    (constantMatrix (F := F) k * A) r c = ∑ j ∈ constantRows k r, A j c := by
  simp only [Matrix.mul_apply, constantMatrix, supportMatrix, constantRows_check,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_mem_eq]

variable [CharP F 2]

lemma constant_equation (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) (k : Fin 4) (r c : Fin 28) :
    (∑ j ∈ constantCols k c, A r j) + (∑ j ∈ constantRows k r, A j c) = 0 := by
  have he := congrArg (fun M : Matrix (Fin 28) (Fin 28) F => M r c) (h k).eq
  rw [mul_constant_entry, constant_mul_entry] at he
  rw [he, CharTwo.add_self_eq_zero]

end Triality.Standard.ElementaryCentralKernel.FixedRootCommutant

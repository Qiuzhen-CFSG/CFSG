module

public import Theory.Representation.HermitianTensorThree.ImageOuter.FieldSections.Basic

/-!
# Elementary matrices in the fixed and moved Hermitian sections

The diagonal and symmetric elementary matrices are fixed by the field swap.
A coefficient of trace one realizes each symmetric off-diagonal matrix as
an actual commutator. All commutators have zero diagonal.

Source: the tensor calculation in Aschbacher–Smith H.4.4(6), printed p.381.
-/

@[expose] public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter.FieldSections
variable (n : ℕ) [NeZero n]

def diagonalUnit (i : Fin 3) : Space n :=
  ⟨Matrix.single i i 1, by ext a b; simp [adjoint, Matrix.single_apply]⟩

def symmetricUnit (i j : Fin 3) : Space n :=
  ⟨Matrix.single i j 1 + Matrix.single j i 1, by
    ext a b
    simp [adjoint, Matrix.single_apply, add_comm]⟩

theorem diagonalUnit_mem_fixed (i : Fin 3) : diagonalUnit n i ∈ fieldFixed n := by
  rw [mem_fieldFixed]
  apply Subtype.ext
  simp [diagonalUnit, fieldSwap_apply]

theorem symmetricUnit_mem_fixed (i j : Fin 3) : symmetricUnit n i j ∈ fieldFixed n := by
  rw [mem_fieldFixed]
  apply Subtype.ext
  simp [symmetricUnit, fieldSwap_apply, add_comm]

theorem exists_sigma_ne : ∃ t : E n, sigma n t ≠ t := by
  by_contra! h
  have hb : Function.Bijective (algebraMap (F n) (E n)) := by
    refine ⟨FaithfulSMul.algebraMap_injective _ _, ?_⟩
    intro t
    exact ⟨⟨t, h t⟩, rfl⟩
  have he := Module.finrank_of_bijective_algebraMap hb
  rw [finrank_E] at he
  contradiction

theorem exists_trace_one : ∃ t : E n, sigma n t + t = 1 := by
  obtain ⟨z, hz⟩ := exists_sigma_ne n
  have hd : sigma n z + z ≠ 0 := by
    intro h
    exact hz (CharTwo.add_eq_zero.mp h)
  refine ⟨z / (sigma n z + z), ?_⟩
  rw [map_div₀, map_add, sigma_involutive]
  rw [add_comm z (sigma n z), ← add_div, div_self hd]

theorem symmetricUnit_mem_moved (i j : Fin 3) : symmetricUnit n i j ∈ moved n := by
  obtain ⟨t, ht⟩ := exists_trace_one n
  let Y : Space n := ⟨Matrix.single i j t + Matrix.single j i (sigma n t), by
    ext a b
    simp only [adjoint, Matrix.map_apply, Matrix.transpose_apply, Matrix.add_apply,
      Matrix.single_apply, map_add, @and_comm (i = b) (j = a), @and_comm (j = b) (i = a)]
    split_ifs <;> simp only [map_zero, sigma_involutive n t, add_zero, zero_add, add_comm]⟩
  refine ⟨Y, ?_⟩
  apply Subtype.ext
  ext a b
  change Y.val b a - Y.val a b = (symmetricUnit n i j).val a b
  dsimp [Y, symmetricUnit]
  simp only [Matrix.single_apply, CharTwo.sub_eq_add]
  simp only [@and_comm (i = b) (j = a), @and_comm (j = b) (i = a)]
  split_ifs <;> simp only [add_zero, zero_add, ht, add_comm t (sigma n t)]

theorem moved_diagonal_zero (X : moved n) (i : Fin 3) : X.val.val i i = 0 := by
  obtain ⟨Y, hY⟩ := X.property
  have h := congrArg (fun Z : Space n => Z.val i i) hY
  change Y.val i i - Y.val i i = X.val.val i i at h
  simpa only [sub_self] using h.symm

theorem diagonalUnit_congruence (A : Mat n) (i a b : Fin 3) :
    (A * (diagonalUnit n i).val * adjoint n A) a b = A a i * sigma n (A b i) := by
  simp [diagonalUnit, Matrix.mul_apply, Matrix.single_apply, adjoint, ite_and]

theorem symmetricUnit_congruence (A : Mat n) (i j a b : Fin 3) :
    (A * (symmetricUnit n i j).val * adjoint n A) a b =
      A a i * sigma n (A b j) + A a j * sigma n (A b i) := by
  simp [symmetricUnit, Matrix.mul_apply, Matrix.single_apply, adjoint, ite_and,
    Finset.sum_add_distrib, mul_add, add_mul]

end Representation.HermitianTensorThree.ImageOuter.FieldSections

module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Descent
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# A right inverse from the square pivot minor of a row section

Selecting columns is multiplication by a column-selection matrix. A right
inverse of the selected square minor therefore gives a right inverse of the
original rectangular matrix. Reindexing the rows preserves the convention
that the kernel rows precede the lifted rows. This is applied to the supplied
539-column minor of the degree-518 tensor section in `Assembly`.

Source: the linear-algebra construction underlying the section certificates
in `Binary/source/README.md`.
-/

@[expose] public section
open Matrix
namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518

theorem rightInverse_of_pivotMinor {m r n : ℕ}
    (N : Matrix (Fin r) (Fin m) (ZMod 2))
    (U : Matrix (Fin n) (Fin m) (ZMod 2))
    (c : Fin (r + n) → Fin m)
    (I : Matrix (Fin (r + n)) (Fin (r + n)) (ZMod 2))
    (h : (Descent.stackedRows N U).submatrix finSumFinEquiv.symm c * I = 1) :
    ∃ R : Matrix (Fin m) (Fin r ⊕ Fin n) (ZMod 2),
      Descent.stackedRows N U * R = 1 := by
  let B := Descent.stackedRows N U
  let S : Matrix (Fin m) (Fin (r + n)) (ZMod 2) :=
    (1 : Matrix (Fin m) (Fin m) (ZMod 2)).submatrix id c
  have hBS : B.submatrix finSumFinEquiv.symm id * S =
      B.submatrix finSumFinEquiv.symm c := by
    simpa only [S, Function.comp_id, Equiv.coe_refl, Equiv.refl_symm,
      Function.id_comp, submatrix_submatrix] using
      mul_submatrix_one (_root_.Equiv.refl (Fin m)) c (B.submatrix finSumFinEquiv.symm id)
  have hBI : B.submatrix finSumFinEquiv.symm id * (S * I) = 1 := by
    rw [← Matrix.mul_assoc, hBS]
    exact h
  refine ⟨(S * I).submatrix id finSumFinEquiv, ?_⟩
  have he := congrArg (fun M : Matrix (Fin (r + n)) (Fin (r + n)) (ZMod 2) =>
    M.submatrix finSumFinEquiv finSumFinEquiv) hBI
  rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id] at he
  simpa only [submatrix_submatrix, Equiv.symm_comp_self, Function.comp_id,
    submatrix_id_id, Matrix.submatrix_one_equiv] using he

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518

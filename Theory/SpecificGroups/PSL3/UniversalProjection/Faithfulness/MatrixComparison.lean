module

public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.Setup

/-!
# Separating the two simple torus parameters in SL₃

The six-letter torus words have diagonal matrix images
`diag(s, s⁻¹, 1)` and `diag(1, t, t⁻¹)`. The first and last diagonal
entries show that their product maps to the identity exactly when both
parameters are one. These calculations concern the existing map into SL₃.

This is the final matrix comparison in Steinberg's proof of Theorem 8(b),
*Lectures on Chevalley Groups*, §6, printed p.71, specialized to type A₂.
It is consumed by the conditional kernel argument in `Faithfulness.lean`.
-/

@[expose] public section

namespace Matrix.PSL3.UniversalProjection.Faithfulness

open Theory.SpecificGroups.LinearHigher SteinbergWords
open Matrix.SpecialLinearGroup
open scoped MatrixGroups

variable {F : Type*} [Field F]

theorem matrixMap_torus_zero_one (t : Fˣ) :
    (matrixMap (torus 0 1 (by decide) t) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(t : F), ((t⁻¹ : Fˣ) : F), 1] := by
  simp only [torus, torusWord, weylWord, map_mul, matrixMap_generator,
    coe_mul, matrixRoot, transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [root, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal,
      Matrix.single, Matrix.one_apply]

theorem matrixMap_torus_one_two (t : Fˣ) :
    (matrixMap (torus 1 2 (by decide) t) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![1, (t : F), ((t⁻¹ : Fˣ) : F)] := by
  simp only [torus, torusWord, weylWord, map_mul, matrixMap_generator,
    coe_mul, matrixRoot, transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [root, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal,
      Matrix.single, Matrix.one_apply]

theorem matrixMap_torus_pair_eq_one_iff (s t : Fˣ) :
    matrixMap (torus 0 1 (by decide) s * torus 1 2 (by decide) t) = 1 ↔
      s = 1 ∧ t = 1 := by
  constructor
  · intro h
    have hm := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) h
    simp only [map_mul, coe_mul, matrixMap_torus_zero_one,
      matrixMap_torus_one_two, Matrix.diagonal_mul_diagonal, coe_one] at hm
    have hs := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 0) hm
    have ht := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 2 2) hm
    simp at hs ht
    exact ⟨hs, ht⟩
  · rintro ⟨rfl, rfl⟩
    simp [torus, torusWord_one generator_relations]

end Matrix.PSL3.UniversalProjection.Faithfulness

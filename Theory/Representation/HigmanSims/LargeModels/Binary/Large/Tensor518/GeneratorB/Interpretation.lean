module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorB.Blocks
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Assembly
/-!
# Interpretation and row consumers of the B-generator checks

The shared packed rows decode to the actual Kronecker generator `ambientB`.
The row soundness lemmas then translate checked XOR equations to rectangular
matrix multiplication using the literal kernel, lifts, correction matrix and
published target generator. No marked-action input is needed for this arithmetic.

Source: ATLAS HSG1-f2r20B0, HSG1-f2r56B0 and HSG1-f2r518B0;
see `Binary/source/README.md`. Original Lean code is Apache-2.0.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorB
open RowArithmetic Thompson.BinaryMatrix Sporadic.LeechRelated.HS

theorem tensorRows_apply (i : Fin 1120) : tensorRows[i.val]! =
    tensorRow 20 56 Twenty.bRows[i.val / 56]! D56.bRows[i.val % 56]! := by
  simp only [tensorRows, List.getElem!_eq_getElem?_getD, List.getElem?_ofFn,
    dif_pos i.isLt, Option.getD_some]

theorem ambient_interpretation : matrix 1120 1120 tensorRows = ambientB := by
  funext i j
  rw [matrix, tensorRows_apply]
  change bit (tensorRow 20 56 Twenty.bRows[i.val / 56]! D56.bRows[i.val % 56]!) j.val =
    bit Twenty.bRows[i.val / 56]! (j.val / 56) * bit D56.bRows[i.val % 56]! (j.val % 56)
  have hj : j.val = 56 * (j.val / 56) + j.val % 56 := by omega
  unfold bit
  conv_lhs => rw [hj, tensorRow_bit 20 56 _ _ _ _ (by omega) (by omega)
    (factor_bound ⟨i.val % 56, by omega⟩)]
  cases (Twenty.bRows[i.val / 56]!).testBit (j.val / 56) <;>
    cases (D56.bRows[i.val % 56]!).testBit (j.val % 56) <;> decide

theorem kernel_row (i : Fin 21) (h : kernelCheck i.val) :
    (kernelMatrix * ambientB) i = (bKernelMatrix * kernelMatrix) i := by
  change blocksCombine ambientBlocks kernelRows[i.val]! =
    combine kernelRows bKernelRows[i.val]! at h
  rw [blocksCombine_eq, ambient_aligned] at h
  rw [← ambient_interpretation]
  exact (vector_combine tensorRows 1120 1120 tensor_length kernelRows[i.val]!).symm.trans
    ((congrArg (vector 1120) h).trans (vector_combine kernelRows 21 1120 kernel_length
      bKernelRows[i.val]!))

theorem lift_row (i : Fin 518) (h : liftCheck i.val) :
    (liftMatrix * ambientB) i =
      (bCorrectionMatrix * kernelMatrix + targetB * liftMatrix) i := by
  change blocksCombine ambientBlocks liftRows[i.val]! =
    combine kernelRows bCorrectionRows[i.val]! ^^^ blocksCombine liftBlocks D518.bRows[i.val]! at h
  rw [blocksCombine_eq, ambient_aligned, blocksCombine_eq, lift_aligned] at h
  have hl := vector_combine tensorRows 1120 1120 tensor_length liftRows[i.val]!
  have hc := vector_combine kernelRows 21 1120 kernel_length bCorrectionRows[i.val]!
  have ht := vector_combine liftRows 518 1120 lift_length D518.bRows[i.val]!
  rw [← ambient_interpretation]
  funext j
  calc
    _ = vector 1120 (combine tensorRows liftRows[i.val]!) j := (congrFun hl j).symm
    _ = vector 1120 (combine kernelRows bCorrectionRows[i.val]!) j +
        vector 1120 (combine liftRows D518.bRows[i.val]!) j := by
      simp only [vector, h, bit_xor]
    _ = _ := congrArg₂ (fun x y : ZMod 2 => x + y) (congrFun hc j) (congrFun ht j)
end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorB

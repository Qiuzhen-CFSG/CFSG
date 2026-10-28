module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.Numerical
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.Interpretations
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.DensityCriterion

/-!
# The rank-one projector for the degree-896 HS matrices

Put H = A+B+omega² I and P = uv, with the shared normalized null pair. The
packed certificates prove Hu = vH = 0, HT = I+P and vT = v. Hence
(H+P)T = I in characteristic two. The finite-ring argument in
`DensityCriterion` places P in the generated algebra. Fullness then needs
only the two independently certified orbit spans.

The data come from the literal ATLAS HSG1-f4r896aB0 matrices and the untrusted
inverse in `Certificates/source/witnesses.json.gz`. Every numerical identity
used below is kernel checked. The only premises for projector membership are
the shared generator re-encodings; their producer is
`qt-k04-hs-896-generator-reencoding`, and the parent matrix-certificate task
owns their discharge and the two orbit spans.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates
open Projector Packed

/-- The checked candidate inverse of the rank-one perturbation. -/
def perturbationInverse : Matrix (Fin 896) (Fin 896) Four := eval 896 inverseRows

theorem singular_mulVec_nullColumn_of_reencoding
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB) : singular.mulVec nullColumn = 0 := by
  rw [← eval_hRows hA hB]
  funext i
  have h := checkDots_get 10 896 uPlanes hRows column_zero_checked i.val
    (by simpa only [hRows_length] using i.isLt)
  rw [dot_eq 10 896 (by decide)] at h
  simpa only [Matrix.mulVec, dotProduct, eval, uPlanes_decode, Pi.zero_apply] using h

theorem nullRow_vecMul_singular_of_reencoding
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB) : Matrix.vecMul nullRow singular = 0 := by
  rw [← eval_hRows hA hB]
  funext j
  have h := congrArg (fun r : Row => decode r j.val) row_zero_checked
  rw [product_eq, decode_rowProduct _ _ 896 hRows_length] at h
  simpa only [Matrix.vecMul, dotProduct, eval, vPlanes_decode,
    show decode (0, 0) j.val = 0 from Base.entry_zero omega j.val, Pi.zero_apply] using h

private theorem nullRow_mul_perturbationInverse :
    Matrix.vecMul nullRow perturbationInverse = nullRow := by
  funext j
  have h := congrArg (fun r : Row => decode r j.val) row_inverse_checked
  rw [product_eq, decode_rowProduct _ _ 896 inverseRows_length] at h
  simpa only [Matrix.vecMul, dotProduct, perturbationInverse, eval, vPlanes_decode] using h

theorem perturbation_mul_inverse_of_reencoding
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB) :
    (singular + Matrix.vecMulVec nullColumn nullRow) * perturbationInverse = 1 := by
  have h := inverse_checked
  rw [eval_hRows hA hB, eval_qRows] at h
  change singular * perturbationInverse = 1 + Matrix.vecMulVec nullColumn nullRow at h
  rw [Matrix.add_mul, h, Matrix.vecMulVec_mul, nullRow_mul_perturbationInverse,
    add_assoc]
  have hz : Matrix.vecMulVec nullColumn nullRow + Matrix.vecMulVec nullColumn nullRow = 0 := by
    funext i j
    exact CharTwo.add_self_eq_zero (nullColumn i * nullRow j)
  rw [hz, add_zero]

/-- Projector membership, with exactly the two independent re-encoding premises. -/
theorem nullProjector_mem_of_reencoding
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB) :
    Matrix.vecMulVec nullColumn nullRow ∈ generated :=
  nullProjector_mem_of_inverse perturbationInverse
    (singular_mulVec_nullColumn_of_reencoding hA hB)
    (nullRow_vecMul_singular_of_reencoding hA hB)
    (perturbation_mul_inverse_of_reencoding hA hB)

/-- Application to the literal generated algebra; the two orbit-span producers
supply the remaining geometric inputs to the parent assembly. -/
theorem full_of_reencoding_of_orbitSpans
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB)
    (hc : columnOrbitSpan = ⊤) (hr : rowOrbitSpan = ⊤) : MatrixAlgebraFull :=
  full_of_nullProjector (nullProjector_mem_of_reencoding hA hB) hc hr

end Representation.HigmanSims.LargeModels.TracePair.Certificates

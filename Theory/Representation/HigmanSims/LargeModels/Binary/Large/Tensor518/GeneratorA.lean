module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Packing

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Kernel

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift000

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift032

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift064

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift096

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift128

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift160

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift192

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift224

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift256

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift288

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift320

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift352

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift384

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift416

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift448

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift480

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Certificates.Lift512

/-!
# The first generator intertwines the actual degree-518 HS tensor section

Kernel-checked packed equalities cover all 21 kernel and 518 lift rows.
`GeneratorA.ambient_matrix` identifies the checked ambient rows with
the literal Kronecker matrix, and `RowArithmetic.vector_combine` converts
those equalities to ordinary rectangular matrix multiplication. The final
application discharges exactly the two A-generator premises of the actual
marked-action assembly; its independent B and pivot premises remain explicit.

Source: R. A. Wilson et al., ATLAS HSG1-f2r20B0, HSG1-f2r56B0 and
HSG1-f2r518B0, and the section in `Binary/source/section518.json`.
Attribution, retained rights, reproduction and measurements are documented in
`GeneratorA/source/README.md`. Original Lean and generation code is Apache-2.0.
-/

public section

namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518

open Thompson.BinaryMatrix RowArithmetic GeneratorA

private theorem packed_kernel (i : Fin 21) :
    combine Blocks.ambientSuffix0 kernelRows[i.val]! =
      combine kernelRows aKernelRows[i.val]! := by
  simpa only [Blocks.kernelAligned] using Certificates.kernel i

private theorem packed_lift (i : Fin 518) :
    combine Blocks.ambientSuffix0 liftRows[i.val]! =
      combine kernelRows aCorrectionRows[i.val]! ^^^ combine liftRows D518.aRows[i.val]! := by
  have hi := i.isLt

  by_cases h256 : i.val < 256
  · by_cases h128 : i.val < 128
    · by_cases h64 : i.val < 64
      · by_cases h32 : i.val < 32
        · have h := Certificates.lift_000 ⟨i.val, by omega⟩
          simpa only [Nat.zero_add, Blocks.kernelAligned, Blocks.liftAligned] using h
        · have h := Certificates.lift_032 ⟨i.val - 32, by omega⟩
          have hx : 32 + (i.val - 32) = i.val := by omega
          rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
          exact h
      · by_cases h96 : i.val < 96
        · have h := Certificates.lift_064 ⟨i.val - 64, by omega⟩
          have hx : 64 + (i.val - 64) = i.val := by omega
          rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
          exact h
        · have h := Certificates.lift_096 ⟨i.val - 96, by omega⟩
          have hx : 96 + (i.val - 96) = i.val := by omega
          rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
          exact h
    · by_cases h192 : i.val < 192
      · by_cases h160 : i.val < 160
        · have h := Certificates.lift_128 ⟨i.val - 128, by omega⟩
          have hx : 128 + (i.val - 128) = i.val := by omega
          rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
          exact h
        · have h := Certificates.lift_160 ⟨i.val - 160, by omega⟩
          have hx : 160 + (i.val - 160) = i.val := by omega
          rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
          exact h
      · by_cases h224 : i.val < 224
        · have h := Certificates.lift_192 ⟨i.val - 192, by omega⟩
          have hx : 192 + (i.val - 192) = i.val := by omega
          rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
          exact h
        · have h := Certificates.lift_224 ⟨i.val - 224, by omega⟩
          have hx : 224 + (i.val - 224) = i.val := by omega
          rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
          exact h
  · by_cases h384 : i.val < 384
    · by_cases h320 : i.val < 320
      · by_cases h288 : i.val < 288
        · have h := Certificates.lift_256 ⟨i.val - 256, by omega⟩
          have hx : 256 + (i.val - 256) = i.val := by omega
          rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
          exact h
        · have h := Certificates.lift_288 ⟨i.val - 288, by omega⟩
          have hx : 288 + (i.val - 288) = i.val := by omega
          rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
          exact h
      · by_cases h352 : i.val < 352
        · have h := Certificates.lift_320 ⟨i.val - 320, by omega⟩
          have hx : 320 + (i.val - 320) = i.val := by omega
          rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
          exact h
        · have h := Certificates.lift_352 ⟨i.val - 352, by omega⟩
          have hx : 352 + (i.val - 352) = i.val := by omega
          rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
          exact h
    · by_cases h448 : i.val < 448
      · by_cases h416 : i.val < 416
        · have h := Certificates.lift_384 ⟨i.val - 384, by omega⟩
          have hx : 384 + (i.val - 384) = i.val := by omega
          rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
          exact h
        · have h := Certificates.lift_416 ⟨i.val - 416, by omega⟩
          have hx : 416 + (i.val - 416) = i.val := by omega
          rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
          exact h
      · by_cases h480 : i.val < 480
        · have h := Certificates.lift_448 ⟨i.val - 448, by omega⟩
          have hx : 448 + (i.val - 448) = i.val := by omega
          rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
          exact h
        · by_cases h512 : i.val < 512
          · have h := Certificates.lift_480 ⟨i.val - 480, by omega⟩
            have hx : 480 + (i.val - 480) = i.val := by omega
            rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
            exact h
          · have h := Certificates.lift_512 ⟨i.val - 512, by omega⟩
            have hx : 512 + (i.val - 512) = i.val := by omega
            rw [hx, Blocks.kernelAligned, Blocks.liftAligned] at h
            exact h

private theorem ambient_length : Blocks.ambientSuffix0.length = 1120 := by decide +kernel
private theorem kernel_length : kernelRows.length = 21 := by decide +kernel
private theorem lift_length : liftRows.length = 518 := by decide +kernel

/-- The actual 21-dimensional kernel is invariant under the first tensor generator. -/
theorem kernel_a : kernelMatrix * ambientA = aKernelMatrix * kernelMatrix := by
  rw [← ambient_matrix]
  funext i j
  have hl := vector_combine Blocks.ambientSuffix0 1120 1120 ambient_length kernelRows[i.val]!
  have hr := vector_combine kernelRows 21 1120 kernel_length aKernelRows[i.val]!
  calc
    _ = vector 1120 (combine Blocks.ambientSuffix0 kernelRows[i.val]!) j :=
      (congrFun hl j).symm
    _ = vector 1120 (combine kernelRows aKernelRows[i.val]!) j := by rw [packed_kernel i]
    _ = _ := congrFun hr j

/-- The lift rows intertwine the first generator modulo the literal kernel,
with exactly the published target matrix and supplied correction coefficients. -/
theorem lift_a : liftMatrix * ambientA =
    aCorrectionMatrix * kernelMatrix + targetA * liftMatrix := by
  rw [← ambient_matrix]
  rw [show targetA = decode 518 D518.aRows from rfl]
  funext i j
  have hl := vector_combine Blocks.ambientSuffix0 1120 1120 ambient_length liftRows[i.val]!
  have hc := vector_combine kernelRows 21 1120 kernel_length aCorrectionRows[i.val]!
  have ht := vector_combine liftRows 518 1120 lift_length D518.aRows[i.val]!
  calc
    _ = vector 1120 (combine Blocks.ambientSuffix0 liftRows[i.val]!) j :=
      (congrFun hl j).symm
    _ = vector 1120 (combine kernelRows aCorrectionRows[i.val]!) j +
        vector 1120 (combine liftRows D518.aRows[i.val]!) j := by
      simp only [vector, packed_lift i, bit_xor]
    _ = _ := congrArg₂ (fun x y : ZMod 2 => x + y) (congrFun hc j) (congrFun ht j)

/-- Application to the actual marked tensor-section descent. The independent
second-generator and pivot certificates are retained for the assembly owner. -/
theorem markedAction_of_generatorA
    (h20 : Nonempty Sporadic.LeechRelated.HS.Twenty.MarkedComparison) (C56 : MarkedAction 0)
    (hNb : kernelMatrix * ambientB = bKernelMatrix * kernelMatrix)
    (hUb : liftMatrix * ambientB = bCorrectionMatrix * kernelMatrix + targetB * liftMatrix)
    (hR : pivotMinor * pivotInverse = 1) : Nonempty (MarkedAction 2) :=
  markedAction_of_certificates h20 C56 kernel_a hNb lift_a hUb hR

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518

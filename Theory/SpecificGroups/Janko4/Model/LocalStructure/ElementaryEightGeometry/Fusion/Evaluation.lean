module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Fusion.Intertwining
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Fusion.Words
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.LiftRelations

/-!
# Native evaluation of the elementary-eight fusion word

The packed products are transported through the faithful original 112-dimensional
representation. The resulting equalities are in the actual max1 subgroup, with
the original multiplication and left kernel corrections.
Source: Kleidman--Wilson (1988), Corollary 2.3.6.
-/

public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Theory.GroupTheory Cardinality KernelCount QuotientCount.Image
open KernelCount.Relations (eval_mul eval_inv representation_x representation_y decoded_product)
open Simplicity.Max1Fusion.KernelOrbits Janko4.GeneratorCertificates
open FusionWords FusionMatrices LiftMatrices
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localX localY basis
local notation "ρ" => representation matrixA_mul_self matrixB_pow_four
local notation "L" => SylowCore.Local

private theorem eval_append (a b : List (Fin 4)) :
    evalWord nativeAlphabet (a ++ b) = evalWord nativeAlphabet a * evalWord nativeAlphabet b := by
  induction a with
  | nil => simp only [List.nil_append, evalWord, one_mul]
  | cons i a ih => simp only [List.cons_append, evalWord, ih, mul_assoc]

private theorem eval_w0 : ρ (evalWord nativeAlphabet w0) = decodeRows xRows := by
  simpa [w0, evalWord, nativeAlphabet] using representation_x matrixA_mul_self matrixB_pow_four
private theorem eval_w1 : ρ (evalWord nativeAlphabet w1) = decodeRows yRows := by
  simpa [w1, evalWord, nativeAlphabet] using representation_y matrixA_mul_self matrixB_pow_four
private theorem eval_w2 : ρ (evalWord nativeAlphabet w2) = decodeRows xRows := by
  change ρ ((localX matrixA_mul_self matrixB_pow_four)⁻¹ * 1) = _
  rw [mul_one, inv_eq_of_mul_eq_one_left (localX_mul_self matrixA_mul_self matrixB_pow_four)]
  exact representation_x _ _
private theorem eval_w3 : ρ (evalWord nativeAlphabet w3) = decodeRows inverseYRows := by
  change ρ ((localY matrixA_mul_self matrixB_pow_four)⁻¹ * 1) = _
  rw [mul_one]
  exact eval_inv ρ (representation_y _ _) (by rw [decoded_product product_inverseY, decode_packedOne])
private theorem eval_w4 : ρ (evalWord nativeAlphabet w4) = decodeRows f4Rows := by
  rw [w4, eval_append]
  exact eval_mul ρ eval_w3 eval_w0 (decoded_product product_f4)
private theorem eval_w5 : ρ (evalWord nativeAlphabet w5) = decodeRows f5Rows := by
  rw [w5, eval_append]
  exact eval_mul ρ eval_w1 eval_w2 (decoded_product product_f5)
private theorem eval_w6 : ρ (evalWord nativeAlphabet w6) = decodeRows f6Rows := by
  rw [w6, eval_append]
  exact eval_mul ρ eval_w1 eval_w0 (decoded_product product_f6)
private theorem eval_w7 : ρ (evalWord nativeAlphabet w7) = decodeRows f7Rows := by
  rw [w7, eval_append]
  exact eval_mul ρ eval_w3 eval_w2 (decoded_product product_f7)
private theorem eval_w8 : ρ (evalWord nativeAlphabet w8) = decodeRows f8Rows := by
  rw [w8, eval_append]
  exact eval_mul ρ eval_w4 eval_w4 (decoded_product product_f8)
private theorem eval_w9 : ρ (evalWord nativeAlphabet w9) = decodeRows f9Rows := by
  rw [w9, eval_append]
  exact eval_mul ρ eval_w5 eval_w5 (decoded_product product_f9)
private theorem eval_w10 : ρ (evalWord nativeAlphabet w10) = decodeRows f10Rows := by
  rw [w10, eval_append]
  exact eval_mul ρ eval_w6 eval_w6 (decoded_product product_f10)
private theorem eval_w11 : ρ (evalWord nativeAlphabet w11) = decodeRows f11Rows := by
  rw [w11, eval_append]
  exact eval_mul ρ eval_w7 eval_w7 (decoded_product product_f11)
private theorem eval_w12 : ρ (evalWord nativeAlphabet w12) = decodeRows f12Rows := by
  rw [w12, eval_append]
  exact eval_mul ρ eval_w6 eval_w8 (decoded_product product_f12)
private theorem eval_w13 : ρ (evalWord nativeAlphabet w13) = decodeRows f13Rows := by
  rw [w13, eval_append]
  exact eval_mul ρ eval_w4 eval_w10 (decoded_product product_f13)
private theorem eval_w14 : ρ (evalWord nativeAlphabet w14) = decodeRows f14Rows := by
  rw [w14, eval_append]
  exact eval_mul ρ eval_w9 eval_w7 (decoded_product product_f14)
private theorem eval_w15 : ρ (evalWord nativeAlphabet w15) = decodeRows f15Rows := by
  rw [w15, eval_append]
  exact eval_mul ρ eval_w12 eval_w13 (decoded_product product_f15)
private theorem eval_w16 : ρ (evalWord nativeAlphabet w16) = decodeRows f16Rows := by
  rw [w16, eval_append]
  exact eval_mul ρ eval_w6 eval_w13 (decoded_product product_f16)
private theorem eval_w17 : ρ (evalWord nativeAlphabet w17) = decodeRows f17Rows := by
  rw [w17, eval_append]
  exact eval_mul ρ eval_w14 eval_w5 (decoded_product product_f17)
private theorem eval_w18 : ρ (evalWord nativeAlphabet w18) = decodeRows f18Rows := by
  rw [w18, eval_append]
  exact eval_mul ρ eval_w3 eval_w4 (decoded_product product_f18)
private theorem eval_w19 : ρ (evalWord nativeAlphabet w19) = decodeRows f19Rows := by
  rw [w19, eval_append]
  exact eval_mul ρ eval_w6 eval_w4 (decoded_product product_f19)
private theorem eval_w20 : ρ (evalWord nativeAlphabet w20) = decodeRows f20Rows := by
  rw [w20, eval_append]
  exact eval_mul ρ eval_w5 eval_w7 (decoded_product product_f20)
private theorem eval_w21 : ρ (evalWord nativeAlphabet w21) = decodeRows f21Rows := by
  rw [w21, eval_append]
  exact eval_mul ρ eval_w8 eval_w15 (decoded_product product_f21)
private theorem eval_w22 : ρ (evalWord nativeAlphabet w22) = decodeRows f22Rows := by
  rw [w22, eval_append]
  exact eval_mul ρ eval_w21 eval_w16 (decoded_product product_f22)
private theorem eval_w23 : ρ (evalWord nativeAlphabet w23) = decodeRows f23Rows := by
  rw [w23, eval_append]
  exact eval_mul ρ eval_w22 eval_w6 (decoded_product product_f23)
private theorem eval_w24 : ρ (evalWord nativeAlphabet w24) = decodeRows f24Rows := by
  rw [w24, eval_append]
  exact eval_mul ρ eval_w23 eval_w17 (decoded_product product_f24)
private theorem eval_w25 : ρ (evalWord nativeAlphabet w25) = decodeRows f25Rows := by
  rw [w25, eval_append]
  exact eval_mul ρ eval_w24 eval_w18 (decoded_product product_f25)
private theorem eval_w26 : ρ (evalWord nativeAlphabet w26) = decodeRows f26Rows := by
  rw [w26, eval_append]
  exact eval_mul ρ eval_w25 eval_w15 (decoded_product product_f26)
private theorem eval_w27 : ρ (evalWord nativeAlphabet w27) = decodeRows f27Rows := by
  rw [w27, eval_append]
  exact eval_mul ρ eval_w26 eval_w5 (decoded_product product_f27)
private theorem eval_w28 : ρ (evalWord nativeAlphabet w28) = decodeRows f28Rows := by
  rw [w28, eval_append]
  exact eval_mul ρ eval_w27 eval_w11 (decoded_product product_f28)
private theorem eval_w29 : ρ (evalWord nativeAlphabet w29) = decodeRows f29Rows := by
  rw [w29, eval_append]
  exact eval_mul ρ eval_w28 eval_w11 (decoded_product product_f29)
private theorem eval_w30 : ρ (evalWord nativeAlphabet w30) = decodeRows f30Rows := by
  rw [w30, eval_append]
  exact eval_mul ρ eval_w29 eval_w9 (decoded_product product_f30)
private theorem eval_w31 : ρ (evalWord nativeAlphabet w31) = decodeRows f31Rows := by
  rw [w31, eval_append]
  exact eval_mul ρ eval_w30 eval_w11 (decoded_product product_f31)
private theorem eval_w32 : ρ (evalWord nativeAlphabet w32) = decodeRows f32Rows := by
  rw [w32, eval_append]
  exact eval_mul ρ eval_w31 eval_w5 (decoded_product product_f32)
private theorem eval_w33 : ρ (evalWord nativeAlphabet w33) = decodeRows f33Rows := by
  rw [w33, eval_append]
  exact eval_mul ρ eval_w32 eval_w8 (decoded_product product_f33)
private theorem eval_w34 : ρ (evalWord nativeAlphabet w34) = decodeRows f34Rows := by
  rw [w34, eval_append]
  exact eval_mul ρ eval_w33 eval_w8 (decoded_product product_f34)
private theorem eval_w35 : ρ (evalWord nativeAlphabet w35) = decodeRows f35Rows := by
  rw [w35, eval_append]
  exact eval_mul ρ eval_w34 eval_w19 (decoded_product product_f35)
private theorem eval_w36 : ρ (evalWord nativeAlphabet w36) = decodeRows f36Rows := by
  rw [w36, eval_append]
  exact eval_mul ρ eval_w35 eval_w16 (decoded_product product_f36)
private theorem eval_w37 : ρ (evalWord nativeAlphabet w37) = decodeRows f37Rows := by
  rw [w37, eval_append]
  exact eval_mul ρ eval_w36 eval_w10 (decoded_product product_f37)
private theorem eval_w38 : ρ (evalWord nativeAlphabet w38) = decodeRows f38Rows := by
  rw [w38, eval_append]
  exact eval_mul ρ eval_w37 eval_w12 (decoded_product product_f38)
private theorem eval_w39 : ρ (evalWord nativeAlphabet w39) = decodeRows f39Rows := by
  rw [w39, eval_append]
  exact eval_mul ρ eval_w38 eval_w4 (decoded_product product_f39)
private theorem eval_w40 : ρ (evalWord nativeAlphabet w40) = decodeRows f40Rows := by
  rw [w40, eval_append]
  exact eval_mul ρ eval_w39 eval_w1 (decoded_product product_f40)
private theorem eval_w41 : ρ (evalWord nativeAlphabet w41) = decodeRows f41Rows := by
  rw [w41, eval_append]
  exact eval_mul ρ eval_w40 eval_w20 (decoded_product product_f41)
private theorem eval_w42 : ρ (evalWord nativeAlphabet w42) = decodeRows f42Rows := by
  rw [w42, eval_append]
  exact eval_mul ρ eval_w41 eval_w9 (decoded_product product_f42)
private theorem eval_w43 : ρ (evalWord nativeAlphabet w43) = decodeRows f43Rows := by
  rw [w43, eval_append]
  exact eval_mul ρ eval_w42 eval_w14 (decoded_product product_f43)
private theorem eval_w44 : ρ (evalWord nativeAlphabet w44) = decodeRows f44Rows := by
  rw [w44, eval_append]
  exact eval_mul ρ eval_w43 eval_w9 (decoded_product product_f44)
private theorem eval_w45 : ρ (evalWord nativeAlphabet w45) = decodeRows f45Rows := by
  rw [w45, eval_append]
  exact eval_mul ρ eval_w44 eval_w17 (decoded_product product_f45)
private theorem eval_w46 : ρ (evalWord nativeAlphabet w46) = decodeRows f46Rows := by
  rw [w46, eval_append]
  exact eval_mul ρ eval_w45 eval_w11 (decoded_product product_f46)
private theorem eval_w47 : ρ (evalWord nativeAlphabet w47) = decodeRows f47Rows := by
  rw [w47, eval_append]
  exact eval_mul ρ eval_w46 eval_w7 (decoded_product product_f47)
private theorem eval_w48 : ρ (evalWord nativeAlphabet w48) = decodeRows f48Rows := by
  rw [w48, eval_append]
  exact eval_mul ρ eval_w47 eval_w9 (decoded_product product_f48)
private theorem eval_w49 : ρ (evalWord nativeAlphabet w49) = decodeRows f49Rows := by
  rw [w49, eval_append]
  exact eval_mul ρ eval_w48 eval_w18 (decoded_product product_f49)
private theorem eval_w50 : ρ (evalWord nativeAlphabet w50) = decodeRows f50Rows := by
  rw [w50, eval_append]
  exact eval_mul ρ eval_w49 eval_w12 (decoded_product product_f50)
private theorem eval_w51 : ρ (evalWord nativeAlphabet w51) = decodeRows f51Rows := by
  rw [w51, eval_append]
  exact eval_mul ρ eval_w50 eval_w12 (decoded_product product_f51)
private theorem eval_w52 : ρ (evalWord nativeAlphabet w52) = decodeRows f52Rows := by
  rw [w52, eval_append]
  exact eval_mul ρ eval_w51 eval_w19 (decoded_product product_f52)
private theorem eval_w53 : ρ (evalWord nativeAlphabet w53) = decodeRows f53Rows := by
  rw [w53, eval_append]
  exact eval_mul ρ eval_w52 eval_w1 (decoded_product product_f53)
private theorem eval_w54 : ρ (evalWord nativeAlphabet w54) = decodeRows f54Rows := by
  rw [w54, eval_append]
  exact eval_mul ρ eval_w53 eval_w9 (decoded_product product_f54)
private theorem eval_w55 : ρ (evalWord nativeAlphabet w55) = decodeRows f55Rows := by
  rw [w55, eval_append]
  exact eval_mul ρ eval_w54 eval_w20 (decoded_product product_f55)
private theorem eval_w56 : ρ (evalWord nativeAlphabet w56) = decodeRows f56Rows := by
  rw [w56, eval_append]
  exact eval_mul ρ eval_w55 eval_w5 (decoded_product product_f56)
private theorem eval_w57 : ρ (evalWord nativeAlphabet w57) = decodeRows f57Rows := by
  rw [w57, eval_append]
  exact eval_mul ρ eval_w56 eval_w3 (decoded_product product_f57)
private theorem eval_w58 : ρ (evalWord nativeAlphabet w58) = decodeRows f58Rows := by
  rw [w58, eval_append]
  exact eval_mul ρ eval_w57 eval_w8 (decoded_product product_f58)

private theorem eval_basis (i : Fin 11) :
    ρ (nativeMask (2^i.val)) = decodeRows (basisRows i) := by
  rw [show nativeMask (2^i.val) = basis matrixA_mul_self matrixB_pow_four i from
    maskValue_basis matrixA_mul_self matrixB_pow_four i]
  exact representation_basis _ _ i
private theorem eval_m9 : ρ (nativeMask 9) = decodeRows m9Rows := by
  rw [show nativeMask 9 = nativeMask 1 * nativeMask 8 from nativeMask_xor 1 8]
  exact eval_mul ρ (eval_basis 0) (eval_basis 3) (decoded_product product_m9)
private theorem eval_m41 : ρ (nativeMask 41) = decodeRows m41Rows := by
  rw [show nativeMask 41 = nativeMask 9 * nativeMask 32 from nativeMask_xor 9 32]
  exact eval_mul ρ eval_m9 (eval_basis 5) (decoded_product product_m41)
private theorem eval_m105 : ρ (nativeMask 105) = decodeRows m105Rows := by
  rw [show nativeMask 105 = nativeMask 41 * nativeMask 64 from nativeMask_xor 41 64]
  exact eval_mul ρ eval_m41 (eval_basis 6) (decoded_product product_m105)
private theorem eval_m1129 : ρ (nativeMask 1129) = decodeRows m1129Rows := by
  rw [show nativeMask 1129 = nativeMask 105 * nativeMask 1024 from nativeMask_xor 105 1024]
  exact eval_mul ρ eval_m105 (eval_basis 10) (decoded_product product_m1129)
private theorem eval_m3 : ρ (nativeMask 3) = decodeRows m3Rows := by
  rw [show nativeMask 3 = nativeMask 1 * nativeMask 2 from nativeMask_xor 1 2]
  exact eval_mul ρ (eval_basis 0) (eval_basis 1) (decoded_product product_m3)
private theorem eval_m7 : ρ (nativeMask 7) = decodeRows m7Rows := by
  rw [show nativeMask 7 = nativeMask 3 * nativeMask 4 from nativeMask_xor 3 4]
  exact eval_mul ρ eval_m3 (eval_basis 2) (decoded_product product_m7)
private theorem eval_m23 : ρ (nativeMask 23) = decodeRows m23Rows := by
  rw [show nativeMask 23 = nativeMask 7 * nativeMask 16 from nativeMask_xor 7 16]
  exact eval_mul ρ eval_m7 (eval_basis 4) (decoded_product product_m23)
private theorem eval_m55 : ρ (nativeMask 55) = decodeRows m55Rows := by
  rw [show nativeMask 55 = nativeMask 23 * nativeMask 32 from nativeMask_xor 23 32]
  exact eval_mul ρ eval_m23 (eval_basis 5) (decoded_product product_m55)
private theorem eval_m311 : ρ (nativeMask 311) = decodeRows m311Rows := by
  rw [show nativeMask 311 = nativeMask 55 * nativeMask 256 from nativeMask_xor 55 256]
  exact eval_mul ρ eval_m55 (eval_basis 8) (decoded_product product_m311)
private theorem eval_m823 : ρ (nativeMask 823) = decodeRows m823Rows := by
  rw [show nativeMask 823 = nativeMask 311 * nativeMask 512 from nativeMask_xor 311 512]
  exact eval_mul ρ eval_m311 (eval_basis 9) (decoded_product product_m823)
private theorem eval_m6 : ρ (nativeMask 6) = decodeRows m6Rows := by
  rw [show nativeMask 6 = nativeMask 2 * nativeMask 4 from nativeMask_xor 2 4]
  exact eval_mul ρ (eval_basis 1) (eval_basis 2) (decoded_product product_m6)
private theorem eval_m14 : ρ (nativeMask 14) = decodeRows m14Rows := by
  rw [show nativeMask 14 = nativeMask 6 * nativeMask 8 from nativeMask_xor 6 8]
  exact eval_mul ρ eval_m6 (eval_basis 3) (decoded_product product_m14)
private theorem eval_m30 : ρ (nativeMask 30) = decodeRows m30Rows := by
  rw [show nativeMask 30 = nativeMask 14 * nativeMask 16 from nativeMask_xor 14 16]
  exact eval_mul ρ eval_m14 (eval_basis 4) (decoded_product product_m30)
private theorem eval_m94 : ρ (nativeMask 94) = decodeRows m94Rows := by
  rw [show nativeMask 94 = nativeMask 30 * nativeMask 64 from nativeMask_xor 30 64]
  exact eval_mul ρ eval_m30 (eval_basis 6) (decoded_product product_m94)
private theorem eval_m350 : ρ (nativeMask 350) = decodeRows m350Rows := by
  rw [show nativeMask 350 = nativeMask 94 * nativeMask 256 from nativeMask_xor 94 256]
  exact eval_mul ρ eval_m94 (eval_basis 8) (decoded_product product_m350)
private theorem eval_m862 : ρ (nativeMask 862) = decodeRows m862Rows := by
  rw [show nativeMask 862 = nativeMask 350 * nativeMask 512 from nativeMask_xor 350 512]
  exact eval_mul ρ eval_m350 (eval_basis 9) (decoded_product product_m862)
private theorem eval_m1886 : ρ (nativeMask 1886) = decodeRows m1886Rows := by
  rw [show nativeMask 1886 = nativeMask 862 * nativeMask 1024 from nativeMask_xor 862 1024]
  exact eval_mul ρ eval_m862 (eval_basis 10) (decoded_product product_m1886)
private theorem eval_m22 : ρ (nativeMask 22) = decodeRows m22Rows := by
  rw [show nativeMask 22 = nativeMask 6 * nativeMask 16 from nativeMask_xor 6 16]
  exact eval_mul ρ eval_m6 (eval_basis 4) (decoded_product product_m22)
private theorem eval_m54 : ρ (nativeMask 54) = decodeRows m54Rows := by
  rw [show nativeMask 54 = nativeMask 22 * nativeMask 32 from nativeMask_xor 22 32]
  exact eval_mul ρ eval_m22 (eval_basis 5) (decoded_product product_m54)
private theorem eval_m310 : ρ (nativeMask 310) = decodeRows m310Rows := by
  rw [show nativeMask 310 = nativeMask 54 * nativeMask 256 from nativeMask_xor 54 256]
  exact eval_mul ρ eval_m54 (eval_basis 8) (decoded_product product_m310)
private theorem eval_m822 : ρ (nativeMask 822) = decodeRows m822Rows := by
  rw [show nativeMask 822 = nativeMask 310 * nativeMask 512 from nativeMask_xor 310 512]
  exact eval_mul ρ eval_m310 (eval_basis 9) (decoded_product product_m822)
private theorem eval_m48 : ρ (nativeMask 48) = decodeRows m48Rows := by
  rw [show nativeMask 48 = nativeMask 16 * nativeMask 32 from nativeMask_xor 16 32]
  exact eval_mul ρ (eval_basis 4) (eval_basis 5) (decoded_product product_m48)
private theorem eval_m304 : ρ (nativeMask 304) = decodeRows m304Rows := by
  rw [show nativeMask 304 = nativeMask 48 * nativeMask 256 from nativeMask_xor 48 256]
  exact eval_mul ρ eval_m48 (eval_basis 8) (decoded_product product_m304)
private theorem eval_m816 : ρ (nativeMask 816) = decodeRows m816Rows := by
  rw [show nativeMask 816 = nativeMask 304 * nativeMask 512 from nativeMask_xor 304 512]
  exact eval_mul ρ eval_m304 (eval_basis 9) (decoded_product product_m816)
private theorem eval_m40 : ρ (nativeMask 40) = decodeRows m40Rows := by
  rw [show nativeMask 40 = nativeMask 8 * nativeMask 32 from nativeMask_xor 8 32]
  exact eval_mul ρ (eval_basis 3) (eval_basis 5) (decoded_product product_m40)
private theorem eval_m104 : ρ (nativeMask 104) = decodeRows m104Rows := by
  rw [show nativeMask 104 = nativeMask 40 * nativeMask 64 from nativeMask_xor 40 64]
  exact eval_mul ρ eval_m40 (eval_basis 6) (decoded_product product_m104)
private theorem eval_m1128 : ρ (nativeMask 1128) = decodeRows m1128Rows := by
  rw [show nativeMask 1128 = nativeMask 104 * nativeMask 1024 from nativeMask_xor 104 1024]
  exact eval_mul ρ eval_m104 (eval_basis 10) (decoded_product product_m1128)

theorem representation_localFusion : ρ localFusion = decodeRows conjugatorRows := by
  rw [localFusion, ← finalWord_eq]
  exact eval_mul ρ (eval_basis 4) eval_w58 (decoded_product product_conjugator)

private theorem decoded_intertwine (a b c : Vector ℕ 112)
    (h : packedMul a b = packedMul c a) :
    decodeRows a * decodeRows b = decodeRows c * decodeRows a :=
  (decode_packedMul a b).symm.trans ((congrArg decodeRows h).trans (decode_packedMul c a))

/-- The four literal images, in corrected lifts and bounded kernel coordinates. -/
@[expose] def fusionTarget : Fin 4 → L :=
  ![nativeMask 1129 * correctedLift 3 * correctedLift 4,
    nativeMask 823 * correctedLift 0 * correctedLift 4,
    nativeMask 1886 * correctedLift 3,
    nativeMask 822 * correctedLift 0 * correctedLift 5]
private theorem eval_t0_1 : ρ (nativeMask 1129 * correctedLift 3) = decodeRows t0_1Rows :=
  eval_mul ρ eval_m1129 (representation_correctedLift 3) (decoded_product product_t0_1)
private theorem eval_t0_2 : ρ (nativeMask 1129 * correctedLift 3 * correctedLift 4) = decodeRows t0_2Rows :=
  eval_mul ρ eval_t0_1 (representation_correctedLift 4) (decoded_product product_t0_2)
private theorem conjugate_lift_0 :
    localFusion * correctedLift 0 * localFusion⁻¹ = fusionTarget 0 := by
  have h : localFusion * correctedLift 0 = fusionTarget 0 * localFusion := by
    apply representation_injective matrixA_mul_self matrixB_pow_four
    rw [map_mul, map_mul, representation_localFusion, representation_correctedLift]
    change decodeRows conjugatorRows * decodeRows l0Rows = ρ (nativeMask 1129 * correctedLift 3 * correctedLift 4) * decodeRows conjugatorRows
    rw [eval_t0_2]
    exact decoded_intertwine _ _ _ intertwine_lift_0
  rw [h, mul_inv_cancel_right]
private theorem eval_t1_0 : ρ (nativeMask 823 * correctedLift 0) = decodeRows t1_0Rows :=
  eval_mul ρ eval_m823 (representation_correctedLift 0) (decoded_product product_t1_0)
private theorem eval_t1_2 : ρ (nativeMask 823 * correctedLift 0 * correctedLift 4) = decodeRows t1_2Rows :=
  eval_mul ρ eval_t1_0 (representation_correctedLift 4) (decoded_product product_t1_2)
private theorem conjugate_lift_1 :
    localFusion * correctedLift 1 * localFusion⁻¹ = fusionTarget 1 := by
  have h : localFusion * correctedLift 1 = fusionTarget 1 * localFusion := by
    apply representation_injective matrixA_mul_self matrixB_pow_four
    rw [map_mul, map_mul, representation_localFusion, representation_correctedLift]
    change decodeRows conjugatorRows * decodeRows l1Rows = ρ (nativeMask 823 * correctedLift 0 * correctedLift 4) * decodeRows conjugatorRows
    rw [eval_t1_2]
    exact decoded_intertwine _ _ _ intertwine_lift_1
  rw [h, mul_inv_cancel_right]
private theorem eval_t2_1 : ρ (nativeMask 1886 * correctedLift 3) = decodeRows t2_1Rows :=
  eval_mul ρ eval_m1886 (representation_correctedLift 3) (decoded_product product_t2_1)
private theorem conjugate_lift_2 :
    localFusion * correctedLift 2 * localFusion⁻¹ = fusionTarget 2 := by
  have h : localFusion * correctedLift 2 = fusionTarget 2 * localFusion := by
    apply representation_injective matrixA_mul_self matrixB_pow_four
    rw [map_mul, map_mul, representation_localFusion, representation_correctedLift]
    change decodeRows conjugatorRows * decodeRows l2Rows = ρ (nativeMask 1886 * correctedLift 3) * decodeRows conjugatorRows
    rw [eval_t2_1]
    exact decoded_intertwine _ _ _ intertwine_lift_2
  rw [h, mul_inv_cancel_right]
private theorem eval_t3_0 : ρ (nativeMask 822 * correctedLift 0) = decodeRows t3_0Rows :=
  eval_mul ρ eval_m822 (representation_correctedLift 0) (decoded_product product_t3_0)
private theorem eval_t3_3 : ρ (nativeMask 822 * correctedLift 0 * correctedLift 5) = decodeRows t3_3Rows :=
  eval_mul ρ eval_t3_0 (representation_correctedLift 5) (decoded_product product_t3_3)
private theorem conjugate_lift_3 :
    localFusion * correctedLift 5 * localFusion⁻¹ = fusionTarget 3 := by
  have h : localFusion * correctedLift 5 = fusionTarget 3 * localFusion := by
    apply representation_injective matrixA_mul_self matrixB_pow_four
    rw [map_mul, map_mul, representation_localFusion, representation_correctedLift]
    change decodeRows conjugatorRows * decodeRows l5Rows = ρ (nativeMask 822 * correctedLift 0 * correctedLift 5) * decodeRows conjugatorRows
    rw [eval_t3_3]
    exact decoded_intertwine _ _ _ intertwine_lift_3
  rw [h, mul_inv_cancel_right]

theorem localFusion_correctedGenerator (j : Fin 4) :
    localFusion * correctedGenerator 0 j * localFusion⁻¹ = fusionTarget j := by
  fin_cases j
  · exact conjugate_lift_0
  · exact conjugate_lift_1
  · exact conjugate_lift_2
  · exact conjugate_lift_3

theorem localFusion_mask_1 :
    localFusion * nativeMask 1 * localFusion⁻¹ = nativeMask 1 := by
  have h : localFusion * nativeMask 1 = nativeMask 1 * localFusion := by
    apply representation_injective matrixA_mul_self matrixB_pow_four
    rw [map_mul, map_mul, representation_localFusion, (show ρ (nativeMask 1) = decodeRows e0Rows from eval_basis 0)]
    exact decoded_intertwine _ _ _ intertwine_mask_1
  rw [h, mul_inv_cancel_right]

theorem localFusion_mask_2 :
    localFusion * nativeMask 2 * localFusion⁻¹ = nativeMask 822 := by
  have h : localFusion * nativeMask 2 = nativeMask 822 * localFusion := by
    apply representation_injective matrixA_mul_self matrixB_pow_four
    rw [map_mul, map_mul, representation_localFusion, (show ρ (nativeMask 2) = decodeRows e1Rows from eval_basis 1), eval_m822]
    exact decoded_intertwine _ _ _ intertwine_mask_2
  rw [h, mul_inv_cancel_right]

theorem localFusion_mask_816 :
    localFusion * nativeMask 816 * localFusion⁻¹ = nativeMask 1128 := by
  have h : localFusion * nativeMask 816 = nativeMask 1128 * localFusion := by
    apply representation_injective matrixA_mul_self matrixB_pow_four
    rw [map_mul, map_mul, representation_localFusion, eval_m816, eval_m1128]
    exact decoded_intertwine _ _ _ intertwine_mask_816
  rw [h, mul_inv_cancel_right]

theorem localFusion_mask_1128 :
    localFusion * nativeMask 1128 * localFusion⁻¹ = nativeMask 4 := by
  have h : localFusion * nativeMask 1128 = nativeMask 4 * localFusion := by
    apply representation_injective matrixA_mul_self matrixB_pow_four
    rw [map_mul, map_mul, representation_localFusion, eval_m1128, (show ρ (nativeMask 4) = decodeRows e2Rows from eval_basis 2)]
    exact decoded_intertwine _ _ _ intertwine_mask_1128
  rw [h, mul_inv_cancel_right]

end Janko4.LocalStructure.ElementaryEightGeometry

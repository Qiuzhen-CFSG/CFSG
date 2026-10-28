module
public import Theory.SpecificGroups.Thompson.TwoRankLower.First
/-! Checked word products for the Thompson elementary eight; see Data. -/
public section
namespace Thompson.TwoRank.Matrices
open InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
set_option Elab.async false
private theorem mul_baseB1_check0 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 0 16 = true := by decide +kernel
private theorem mul_baseB1_check1 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 16 16 = true := by decide +kernel
private theorem mul_baseB1_check2 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 32 16 = true := by decide +kernel
private theorem mul_baseB1_check3 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 48 16 = true := by decide +kernel
private theorem mul_baseB1_check4 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 64 16 = true := by decide +kernel
private theorem mul_baseB1_check5 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 80 16 = true := by decide +kernel
private theorem mul_baseB1_check6 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 96 16 = true := by decide +kernel
private theorem mul_baseB1_check7 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 112 16 = true := by decide +kernel
private theorem mul_baseB1_check8 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 128 16 = true := by decide +kernel
private theorem mul_baseB1_check9 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 144 16 = true := by decide +kernel
private theorem mul_baseB1_check10 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 160 16 = true := by decide +kernel
private theorem mul_baseB1_check11 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 176 16 = true := by decide +kernel
private theorem mul_baseB1_check12 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 192 16 = true := by decide +kernel
private theorem mul_baseB1_check13 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 208 16 = true := by decide +kernel
private theorem mul_baseB1_check14 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 224 16 = true := by decide +kernel
private theorem mul_baseB1_check15 : checkRange (fun i => BinaryMatrix.listProduct y[i]! x.toList 0 == baseB1[i]!) 240 8 = true := by decide +kernel
theorem mul_baseB1 : BinaryMatrix.decode 248 y * BinaryMatrix.decode 248 x = BinaryMatrix.decode 248 baseB1 := by
  apply checked_mul 248 y x baseB1 rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseB1_check0) (mul_baseB1_check1)) (checkRange_append (m := 16) (n := 16) (mul_baseB1_check2) (mul_baseB1_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseB1_check4) (mul_baseB1_check5)) (checkRange_append (m := 16) (n := 16) (mul_baseB1_check6) (mul_baseB1_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseB1_check8) (mul_baseB1_check9)) (checkRange_append (m := 16) (n := 16) (mul_baseB1_check10) (mul_baseB1_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_baseB1_check12) (mul_baseB1_check13)) (checkRange_append (m := 16) (n := 8) (mul_baseB1_check14) (mul_baseB1_check15))))
private theorem mul_baseB2_check0 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 0 16 = true := by decide +kernel
private theorem mul_baseB2_check1 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 16 16 = true := by decide +kernel
private theorem mul_baseB2_check2 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 32 16 = true := by decide +kernel
private theorem mul_baseB2_check3 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 48 16 = true := by decide +kernel
private theorem mul_baseB2_check4 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 64 16 = true := by decide +kernel
private theorem mul_baseB2_check5 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 80 16 = true := by decide +kernel
private theorem mul_baseB2_check6 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 96 16 = true := by decide +kernel
private theorem mul_baseB2_check7 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 112 16 = true := by decide +kernel
private theorem mul_baseB2_check8 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 128 16 = true := by decide +kernel
private theorem mul_baseB2_check9 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 144 16 = true := by decide +kernel
private theorem mul_baseB2_check10 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 160 16 = true := by decide +kernel
private theorem mul_baseB2_check11 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 176 16 = true := by decide +kernel
private theorem mul_baseB2_check12 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 192 16 = true := by decide +kernel
private theorem mul_baseB2_check13 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 208 16 = true := by decide +kernel
private theorem mul_baseB2_check14 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 224 16 = true := by decide +kernel
private theorem mul_baseB2_check15 : checkRange (fun i => BinaryMatrix.listProduct baseB1[i]! y2.toList 0 == baseB2[i]!) 240 8 = true := by decide +kernel
theorem mul_baseB2 : BinaryMatrix.decode 248 baseB1 * BinaryMatrix.decode 248 y2 = BinaryMatrix.decode 248 baseB2 := by
  apply checked_mul 248 baseB1 y2 baseB2 rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseB2_check0) (mul_baseB2_check1)) (checkRange_append (m := 16) (n := 16) (mul_baseB2_check2) (mul_baseB2_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseB2_check4) (mul_baseB2_check5)) (checkRange_append (m := 16) (n := 16) (mul_baseB2_check6) (mul_baseB2_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseB2_check8) (mul_baseB2_check9)) (checkRange_append (m := 16) (n := 16) (mul_baseB2_check10) (mul_baseB2_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_baseB2_check12) (mul_baseB2_check13)) (checkRange_append (m := 16) (n := 8) (mul_baseB2_check14) (mul_baseB2_check15))))
private theorem mul_baseB_check0 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 0 16 = true := by decide +kernel
private theorem mul_baseB_check1 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 16 16 = true := by decide +kernel
private theorem mul_baseB_check2 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 32 16 = true := by decide +kernel
private theorem mul_baseB_check3 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 48 16 = true := by decide +kernel
private theorem mul_baseB_check4 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 64 16 = true := by decide +kernel
private theorem mul_baseB_check5 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 80 16 = true := by decide +kernel
private theorem mul_baseB_check6 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 96 16 = true := by decide +kernel
private theorem mul_baseB_check7 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 112 16 = true := by decide +kernel
private theorem mul_baseB_check8 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 128 16 = true := by decide +kernel
private theorem mul_baseB_check9 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 144 16 = true := by decide +kernel
private theorem mul_baseB_check10 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 160 16 = true := by decide +kernel
private theorem mul_baseB_check11 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 176 16 = true := by decide +kernel
private theorem mul_baseB_check12 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 192 16 = true := by decide +kernel
private theorem mul_baseB_check13 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 208 16 = true := by decide +kernel
private theorem mul_baseB_check14 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 224 16 = true := by decide +kernel
private theorem mul_baseB_check15 : checkRange (fun i => BinaryMatrix.listProduct baseB2[i]! x.toList 0 == baseB[i]!) 240 8 = true := by decide +kernel
theorem mul_baseB : BinaryMatrix.decode 248 baseB2 * BinaryMatrix.decode 248 x = BinaryMatrix.decode 248 baseB := by
  apply checked_mul 248 baseB2 x baseB rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseB_check0) (mul_baseB_check1)) (checkRange_append (m := 16) (n := 16) (mul_baseB_check2) (mul_baseB_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseB_check4) (mul_baseB_check5)) (checkRange_append (m := 16) (n := 16) (mul_baseB_check6) (mul_baseB_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseB_check8) (mul_baseB_check9)) (checkRange_append (m := 16) (n := 16) (mul_baseB_check10) (mul_baseB_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_baseB_check12) (mul_baseB_check13)) (checkRange_append (m := 16) (n := 8) (mul_baseB_check14) (mul_baseB_check15))))
private theorem mul_baseBsq_check0 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 0 16 = true := by decide +kernel
private theorem mul_baseBsq_check1 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 16 16 = true := by decide +kernel
private theorem mul_baseBsq_check2 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 32 16 = true := by decide +kernel
private theorem mul_baseBsq_check3 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 48 16 = true := by decide +kernel
private theorem mul_baseBsq_check4 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 64 16 = true := by decide +kernel
private theorem mul_baseBsq_check5 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 80 16 = true := by decide +kernel
private theorem mul_baseBsq_check6 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 96 16 = true := by decide +kernel
private theorem mul_baseBsq_check7 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 112 16 = true := by decide +kernel
private theorem mul_baseBsq_check8 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 128 16 = true := by decide +kernel
private theorem mul_baseBsq_check9 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 144 16 = true := by decide +kernel
private theorem mul_baseBsq_check10 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 160 16 = true := by decide +kernel
private theorem mul_baseBsq_check11 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 176 16 = true := by decide +kernel
private theorem mul_baseBsq_check12 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 192 16 = true := by decide +kernel
private theorem mul_baseBsq_check13 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 208 16 = true := by decide +kernel
private theorem mul_baseBsq_check14 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 224 16 = true := by decide +kernel
private theorem mul_baseBsq_check15 : checkRange (fun i => BinaryMatrix.listProduct baseB[i]! baseB.toList 0 == baseBsq[i]!) 240 8 = true := by decide +kernel
theorem mul_baseBsq : BinaryMatrix.decode 248 baseB * BinaryMatrix.decode 248 baseB = BinaryMatrix.decode 248 baseBsq := by
  apply checked_mul 248 baseB baseB baseBsq rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseBsq_check0) (mul_baseBsq_check1)) (checkRange_append (m := 16) (n := 16) (mul_baseBsq_check2) (mul_baseBsq_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseBsq_check4) (mul_baseBsq_check5)) (checkRange_append (m := 16) (n := 16) (mul_baseBsq_check6) (mul_baseBsq_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseBsq_check8) (mul_baseBsq_check9)) (checkRange_append (m := 16) (n := 16) (mul_baseBsq_check10) (mul_baseBsq_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_baseBsq_check12) (mul_baseBsq_check13)) (checkRange_append (m := 16) (n := 8) (mul_baseBsq_check14) (mul_baseBsq_check15))))
private theorem mul_baseB4_check0 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 0 16 = true := by decide +kernel
private theorem mul_baseB4_check1 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 16 16 = true := by decide +kernel
private theorem mul_baseB4_check2 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 32 16 = true := by decide +kernel
private theorem mul_baseB4_check3 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 48 16 = true := by decide +kernel
private theorem mul_baseB4_check4 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 64 16 = true := by decide +kernel
private theorem mul_baseB4_check5 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 80 16 = true := by decide +kernel
private theorem mul_baseB4_check6 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 96 16 = true := by decide +kernel
private theorem mul_baseB4_check7 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 112 16 = true := by decide +kernel
private theorem mul_baseB4_check8 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 128 16 = true := by decide +kernel
private theorem mul_baseB4_check9 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 144 16 = true := by decide +kernel
private theorem mul_baseB4_check10 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 160 16 = true := by decide +kernel
private theorem mul_baseB4_check11 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 176 16 = true := by decide +kernel
private theorem mul_baseB4_check12 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 192 16 = true := by decide +kernel
private theorem mul_baseB4_check13 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 208 16 = true := by decide +kernel
private theorem mul_baseB4_check14 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 224 16 = true := by decide +kernel
private theorem mul_baseB4_check15 : checkRange (fun i => BinaryMatrix.listProduct baseBsq[i]! baseBsq.toList 0 == baseB4[i]!) 240 8 = true := by decide +kernel
theorem mul_baseB4 : BinaryMatrix.decode 248 baseBsq * BinaryMatrix.decode 248 baseBsq = BinaryMatrix.decode 248 baseB4 := by
  apply checked_mul 248 baseBsq baseBsq baseB4 rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseB4_check0) (mul_baseB4_check1)) (checkRange_append (m := 16) (n := 16) (mul_baseB4_check2) (mul_baseB4_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseB4_check4) (mul_baseB4_check5)) (checkRange_append (m := 16) (n := 16) (mul_baseB4_check6) (mul_baseB4_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseB4_check8) (mul_baseB4_check9)) (checkRange_append (m := 16) (n := 16) (mul_baseB4_check10) (mul_baseB4_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_baseB4_check12) (mul_baseB4_check13)) (checkRange_append (m := 16) (n := 8) (mul_baseB4_check14) (mul_baseB4_check15))))
private theorem mul_baseB8_check0 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 0 16 = true := by decide +kernel
private theorem mul_baseB8_check1 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 16 16 = true := by decide +kernel
private theorem mul_baseB8_check2 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 32 16 = true := by decide +kernel
private theorem mul_baseB8_check3 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 48 16 = true := by decide +kernel
private theorem mul_baseB8_check4 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 64 16 = true := by decide +kernel
private theorem mul_baseB8_check5 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 80 16 = true := by decide +kernel
private theorem mul_baseB8_check6 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 96 16 = true := by decide +kernel
private theorem mul_baseB8_check7 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 112 16 = true := by decide +kernel
private theorem mul_baseB8_check8 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 128 16 = true := by decide +kernel
private theorem mul_baseB8_check9 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 144 16 = true := by decide +kernel
private theorem mul_baseB8_check10 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 160 16 = true := by decide +kernel
private theorem mul_baseB8_check11 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 176 16 = true := by decide +kernel
private theorem mul_baseB8_check12 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 192 16 = true := by decide +kernel
private theorem mul_baseB8_check13 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 208 16 = true := by decide +kernel
private theorem mul_baseB8_check14 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 224 16 = true := by decide +kernel
private theorem mul_baseB8_check15 : checkRange (fun i => BinaryMatrix.listProduct baseB4[i]! baseB4.toList 0 == baseB8[i]!) 240 8 = true := by decide +kernel
theorem mul_baseB8 : BinaryMatrix.decode 248 baseB4 * BinaryMatrix.decode 248 baseB4 = BinaryMatrix.decode 248 baseB8 := by
  apply checked_mul 248 baseB4 baseB4 baseB8 rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseB8_check0) (mul_baseB8_check1)) (checkRange_append (m := 16) (n := 16) (mul_baseB8_check2) (mul_baseB8_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseB8_check4) (mul_baseB8_check5)) (checkRange_append (m := 16) (n := 16) (mul_baseB8_check6) (mul_baseB8_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseB8_check8) (mul_baseB8_check9)) (checkRange_append (m := 16) (n := 16) (mul_baseB8_check10) (mul_baseB8_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_baseB8_check12) (mul_baseB8_check13)) (checkRange_append (m := 16) (n := 8) (mul_baseB8_check14) (mul_baseB8_check15))))
private theorem mul_b_check0 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 0 16 = true := by decide +kernel
private theorem mul_b_check1 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 16 16 = true := by decide +kernel
private theorem mul_b_check2 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 32 16 = true := by decide +kernel
private theorem mul_b_check3 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 48 16 = true := by decide +kernel
private theorem mul_b_check4 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 64 16 = true := by decide +kernel
private theorem mul_b_check5 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 80 16 = true := by decide +kernel
private theorem mul_b_check6 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 96 16 = true := by decide +kernel
private theorem mul_b_check7 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 112 16 = true := by decide +kernel
private theorem mul_b_check8 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 128 16 = true := by decide +kernel
private theorem mul_b_check9 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 144 16 = true := by decide +kernel
private theorem mul_b_check10 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 160 16 = true := by decide +kernel
private theorem mul_b_check11 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 176 16 = true := by decide +kernel
private theorem mul_b_check12 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 192 16 = true := by decide +kernel
private theorem mul_b_check13 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 208 16 = true := by decide +kernel
private theorem mul_b_check14 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 224 16 = true := by decide +kernel
private theorem mul_b_check15 : checkRange (fun i => BinaryMatrix.listProduct baseB8[i]! baseB.toList 0 == b[i]!) 240 8 = true := by decide +kernel
theorem mul_b : BinaryMatrix.decode 248 baseB8 * BinaryMatrix.decode 248 baseB = BinaryMatrix.decode 248 b := by
  apply checked_mul 248 baseB8 baseB b rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_b_check0) (mul_b_check1)) (checkRange_append (m := 16) (n := 16) (mul_b_check2) (mul_b_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_b_check4) (mul_b_check5)) (checkRange_append (m := 16) (n := 16) (mul_b_check6) (mul_b_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_b_check8) (mul_b_check9)) (checkRange_append (m := 16) (n := 16) (mul_b_check10) (mul_b_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_b_check12) (mul_b_check13)) (checkRange_append (m := 16) (n := 8) (mul_b_check14) (mul_b_check15))))
theorem witness_baseB1 : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 baseB1 := witness_mul witness_y witness_x mul_baseB1
theorem witness_baseB2 : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 baseB2 := witness_mul witness_baseB1 witness_y2 mul_baseB2
theorem witness_baseB : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 baseB := witness_mul witness_baseB2 witness_x mul_baseB
theorem witness_baseBsq : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 baseBsq := witness_mul witness_baseB witness_baseB mul_baseBsq
theorem witness_baseB4 : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 baseB4 := witness_mul witness_baseBsq witness_baseBsq mul_baseB4
theorem witness_baseB8 : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 baseB8 := witness_mul witness_baseB4 witness_baseB4 mul_baseB8
theorem witness_b : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 b := witness_mul witness_baseB8 witness_baseB mul_b
end Thompson.TwoRank.Matrices

module
public import Theory.SpecificGroups.Thompson.TwoRankLower.First
/-! Checked word products for the Thompson elementary eight; see Data. -/
public section
namespace Thompson.TwoRank.Matrices
open InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
set_option Elab.async false
private theorem mul_xy2_check0 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 0 16 = true := by decide +kernel
private theorem mul_xy2_check1 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 16 16 = true := by decide +kernel
private theorem mul_xy2_check2 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 32 16 = true := by decide +kernel
private theorem mul_xy2_check3 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 48 16 = true := by decide +kernel
private theorem mul_xy2_check4 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 64 16 = true := by decide +kernel
private theorem mul_xy2_check5 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 80 16 = true := by decide +kernel
private theorem mul_xy2_check6 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 96 16 = true := by decide +kernel
private theorem mul_xy2_check7 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 112 16 = true := by decide +kernel
private theorem mul_xy2_check8 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 128 16 = true := by decide +kernel
private theorem mul_xy2_check9 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 144 16 = true := by decide +kernel
private theorem mul_xy2_check10 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 160 16 = true := by decide +kernel
private theorem mul_xy2_check11 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 176 16 = true := by decide +kernel
private theorem mul_xy2_check12 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 192 16 = true := by decide +kernel
private theorem mul_xy2_check13 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 208 16 = true := by decide +kernel
private theorem mul_xy2_check14 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 224 16 = true := by decide +kernel
private theorem mul_xy2_check15 : checkRange (fun i => BinaryMatrix.listProduct xy[i]! xy.toList 0 == xy2[i]!) 240 8 = true := by decide +kernel
theorem mul_xy2 : BinaryMatrix.decode 248 xy * BinaryMatrix.decode 248 xy = BinaryMatrix.decode 248 xy2 := by
  apply checked_mul 248 xy xy xy2 rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_xy2_check0) (mul_xy2_check1)) (checkRange_append (m := 16) (n := 16) (mul_xy2_check2) (mul_xy2_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_xy2_check4) (mul_xy2_check5)) (checkRange_append (m := 16) (n := 16) (mul_xy2_check6) (mul_xy2_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_xy2_check8) (mul_xy2_check9)) (checkRange_append (m := 16) (n := 16) (mul_xy2_check10) (mul_xy2_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_xy2_check12) (mul_xy2_check13)) (checkRange_append (m := 16) (n := 8) (mul_xy2_check14) (mul_xy2_check15))))
private theorem mul_xy3_check0 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 0 16 = true := by decide +kernel
private theorem mul_xy3_check1 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 16 16 = true := by decide +kernel
private theorem mul_xy3_check2 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 32 16 = true := by decide +kernel
private theorem mul_xy3_check3 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 48 16 = true := by decide +kernel
private theorem mul_xy3_check4 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 64 16 = true := by decide +kernel
private theorem mul_xy3_check5 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 80 16 = true := by decide +kernel
private theorem mul_xy3_check6 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 96 16 = true := by decide +kernel
private theorem mul_xy3_check7 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 112 16 = true := by decide +kernel
private theorem mul_xy3_check8 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 128 16 = true := by decide +kernel
private theorem mul_xy3_check9 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 144 16 = true := by decide +kernel
private theorem mul_xy3_check10 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 160 16 = true := by decide +kernel
private theorem mul_xy3_check11 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 176 16 = true := by decide +kernel
private theorem mul_xy3_check12 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 192 16 = true := by decide +kernel
private theorem mul_xy3_check13 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 208 16 = true := by decide +kernel
private theorem mul_xy3_check14 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 224 16 = true := by decide +kernel
private theorem mul_xy3_check15 : checkRange (fun i => BinaryMatrix.listProduct xy2[i]! xy.toList 0 == xy3[i]!) 240 8 = true := by decide +kernel
theorem mul_xy3 : BinaryMatrix.decode 248 xy2 * BinaryMatrix.decode 248 xy = BinaryMatrix.decode 248 xy3 := by
  apply checked_mul 248 xy2 xy xy3 rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_xy3_check0) (mul_xy3_check1)) (checkRange_append (m := 16) (n := 16) (mul_xy3_check2) (mul_xy3_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_xy3_check4) (mul_xy3_check5)) (checkRange_append (m := 16) (n := 16) (mul_xy3_check6) (mul_xy3_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_xy3_check8) (mul_xy3_check9)) (checkRange_append (m := 16) (n := 16) (mul_xy3_check10) (mul_xy3_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_xy3_check12) (mul_xy3_check13)) (checkRange_append (m := 16) (n := 8) (mul_xy3_check14) (mul_xy3_check15))))
private theorem mul_c_check0 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 0 16 = true := by decide +kernel
private theorem mul_c_check1 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 16 16 = true := by decide +kernel
private theorem mul_c_check2 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 32 16 = true := by decide +kernel
private theorem mul_c_check3 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 48 16 = true := by decide +kernel
private theorem mul_c_check4 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 64 16 = true := by decide +kernel
private theorem mul_c_check5 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 80 16 = true := by decide +kernel
private theorem mul_c_check6 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 96 16 = true := by decide +kernel
private theorem mul_c_check7 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 112 16 = true := by decide +kernel
private theorem mul_c_check8 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 128 16 = true := by decide +kernel
private theorem mul_c_check9 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 144 16 = true := by decide +kernel
private theorem mul_c_check10 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 160 16 = true := by decide +kernel
private theorem mul_c_check11 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 176 16 = true := by decide +kernel
private theorem mul_c_check12 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 192 16 = true := by decide +kernel
private theorem mul_c_check13 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 208 16 = true := by decide +kernel
private theorem mul_c_check14 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 224 16 = true := by decide +kernel
private theorem mul_c_check15 : checkRange (fun i => BinaryMatrix.listProduct xy3[i]! xy3.toList 0 == c[i]!) 240 8 = true := by decide +kernel
theorem mul_c : BinaryMatrix.decode 248 xy3 * BinaryMatrix.decode 248 xy3 = BinaryMatrix.decode 248 c := by
  apply checked_mul 248 xy3 xy3 c rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_c_check0) (mul_c_check1)) (checkRange_append (m := 16) (n := 16) (mul_c_check2) (mul_c_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_c_check4) (mul_c_check5)) (checkRange_append (m := 16) (n := 16) (mul_c_check6) (mul_c_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_c_check8) (mul_c_check9)) (checkRange_append (m := 16) (n := 16) (mul_c_check10) (mul_c_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_c_check12) (mul_c_check13)) (checkRange_append (m := 16) (n := 8) (mul_c_check14) (mul_c_check15))))
theorem witness_xy2 : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 xy2 := witness_mul witness_xy witness_xy mul_xy2
theorem witness_xy3 : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 xy3 := witness_mul witness_xy2 witness_xy mul_xy3
theorem witness_c : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 c := witness_mul witness_xy3 witness_xy3 mul_c
end Thompson.TwoRank.Matrices

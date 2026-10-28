module
public import Theory.SpecificGroups.Thompson.TwoRankLower.Data
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
/-! Checked word products for the Thompson elementary eight; see Data. -/
public section
namespace Thompson.TwoRank.Matrices
open InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
theorem witness_mul {a b c : Rows}
    (ha : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 a)
    (hb : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 b)
    (hm : BinaryMatrix.decode 248 a * BinaryMatrix.decode 248 b = BinaryMatrix.decode 248 c) :
    ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 c := by
  obtain ⟨g,hg⟩ := ha
  obtain ⟨f,hf⟩ := hb
  exact ⟨g*f, by rw [map_mul,hg,hf,hm]⟩
theorem witness_x : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 x :=
  ⟨InvolutionCentralizer.AlternatingQuotient.wordA, InvolutionCentralizer.AlternatingQuotient.matrixHom_wordA⟩
theorem witness_y : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 y :=
  ⟨InvolutionCentralizer.AlternatingQuotient.wordB, InvolutionCentralizer.AlternatingQuotient.matrixHom_wordB⟩
set_option Elab.async false
private theorem mul_y2_check0 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 0 16 = true := by decide +kernel
private theorem mul_y2_check1 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 16 16 = true := by decide +kernel
private theorem mul_y2_check2 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 32 16 = true := by decide +kernel
private theorem mul_y2_check3 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 48 16 = true := by decide +kernel
private theorem mul_y2_check4 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 64 16 = true := by decide +kernel
private theorem mul_y2_check5 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 80 16 = true := by decide +kernel
private theorem mul_y2_check6 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 96 16 = true := by decide +kernel
private theorem mul_y2_check7 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 112 16 = true := by decide +kernel
private theorem mul_y2_check8 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 128 16 = true := by decide +kernel
private theorem mul_y2_check9 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 144 16 = true := by decide +kernel
private theorem mul_y2_check10 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 160 16 = true := by decide +kernel
private theorem mul_y2_check11 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 176 16 = true := by decide +kernel
private theorem mul_y2_check12 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 192 16 = true := by decide +kernel
private theorem mul_y2_check13 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 208 16 = true := by decide +kernel
private theorem mul_y2_check14 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 224 16 = true := by decide +kernel
private theorem mul_y2_check15 : checkRange (fun i => BinaryMatrix.listProduct y[i]! y.toList 0 == y2[i]!) 240 8 = true := by decide +kernel
theorem mul_y2 : BinaryMatrix.decode 248 y * BinaryMatrix.decode 248 y = BinaryMatrix.decode 248 y2 := by
  apply checked_mul 248 y y y2 rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_y2_check0) (mul_y2_check1)) (checkRange_append (m := 16) (n := 16) (mul_y2_check2) (mul_y2_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_y2_check4) (mul_y2_check5)) (checkRange_append (m := 16) (n := 16) (mul_y2_check6) (mul_y2_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_y2_check8) (mul_y2_check9)) (checkRange_append (m := 16) (n := 16) (mul_y2_check10) (mul_y2_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_y2_check12) (mul_y2_check13)) (checkRange_append (m := 16) (n := 8) (mul_y2_check14) (mul_y2_check15))))
private theorem mul_y3_check0 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 0 16 = true := by decide +kernel
private theorem mul_y3_check1 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 16 16 = true := by decide +kernel
private theorem mul_y3_check2 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 32 16 = true := by decide +kernel
private theorem mul_y3_check3 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 48 16 = true := by decide +kernel
private theorem mul_y3_check4 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 64 16 = true := by decide +kernel
private theorem mul_y3_check5 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 80 16 = true := by decide +kernel
private theorem mul_y3_check6 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 96 16 = true := by decide +kernel
private theorem mul_y3_check7 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 112 16 = true := by decide +kernel
private theorem mul_y3_check8 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 128 16 = true := by decide +kernel
private theorem mul_y3_check9 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 144 16 = true := by decide +kernel
private theorem mul_y3_check10 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 160 16 = true := by decide +kernel
private theorem mul_y3_check11 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 176 16 = true := by decide +kernel
private theorem mul_y3_check12 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 192 16 = true := by decide +kernel
private theorem mul_y3_check13 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 208 16 = true := by decide +kernel
private theorem mul_y3_check14 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 224 16 = true := by decide +kernel
private theorem mul_y3_check15 : checkRange (fun i => BinaryMatrix.listProduct y2[i]! y.toList 0 == y3[i]!) 240 8 = true := by decide +kernel
theorem mul_y3 : BinaryMatrix.decode 248 y2 * BinaryMatrix.decode 248 y = BinaryMatrix.decode 248 y3 := by
  apply checked_mul 248 y2 y y3 rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_y3_check0) (mul_y3_check1)) (checkRange_append (m := 16) (n := 16) (mul_y3_check2) (mul_y3_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_y3_check4) (mul_y3_check5)) (checkRange_append (m := 16) (n := 16) (mul_y3_check6) (mul_y3_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_y3_check8) (mul_y3_check9)) (checkRange_append (m := 16) (n := 16) (mul_y3_check10) (mul_y3_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_y3_check12) (mul_y3_check13)) (checkRange_append (m := 16) (n := 8) (mul_y3_check14) (mul_y3_check15))))
private theorem mul_xy_check0 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 0 16 = true := by decide +kernel
private theorem mul_xy_check1 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 16 16 = true := by decide +kernel
private theorem mul_xy_check2 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 32 16 = true := by decide +kernel
private theorem mul_xy_check3 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 48 16 = true := by decide +kernel
private theorem mul_xy_check4 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 64 16 = true := by decide +kernel
private theorem mul_xy_check5 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 80 16 = true := by decide +kernel
private theorem mul_xy_check6 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 96 16 = true := by decide +kernel
private theorem mul_xy_check7 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 112 16 = true := by decide +kernel
private theorem mul_xy_check8 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 128 16 = true := by decide +kernel
private theorem mul_xy_check9 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 144 16 = true := by decide +kernel
private theorem mul_xy_check10 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 160 16 = true := by decide +kernel
private theorem mul_xy_check11 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 176 16 = true := by decide +kernel
private theorem mul_xy_check12 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 192 16 = true := by decide +kernel
private theorem mul_xy_check13 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 208 16 = true := by decide +kernel
private theorem mul_xy_check14 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 224 16 = true := by decide +kernel
private theorem mul_xy_check15 : checkRange (fun i => BinaryMatrix.listProduct x[i]! y.toList 0 == xy[i]!) 240 8 = true := by decide +kernel
theorem mul_xy : BinaryMatrix.decode 248 x * BinaryMatrix.decode 248 y = BinaryMatrix.decode 248 xy := by
  apply checked_mul 248 x y xy rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_xy_check0) (mul_xy_check1)) (checkRange_append (m := 16) (n := 16) (mul_xy_check2) (mul_xy_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_xy_check4) (mul_xy_check5)) (checkRange_append (m := 16) (n := 16) (mul_xy_check6) (mul_xy_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_xy_check8) (mul_xy_check9)) (checkRange_append (m := 16) (n := 16) (mul_xy_check10) (mul_xy_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_xy_check12) (mul_xy_check13)) (checkRange_append (m := 16) (n := 8) (mul_xy_check14) (mul_xy_check15))))
private theorem mul_baseA1_check0 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 0 16 = true := by decide +kernel
private theorem mul_baseA1_check1 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 16 16 = true := by decide +kernel
private theorem mul_baseA1_check2 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 32 16 = true := by decide +kernel
private theorem mul_baseA1_check3 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 48 16 = true := by decide +kernel
private theorem mul_baseA1_check4 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 64 16 = true := by decide +kernel
private theorem mul_baseA1_check5 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 80 16 = true := by decide +kernel
private theorem mul_baseA1_check6 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 96 16 = true := by decide +kernel
private theorem mul_baseA1_check7 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 112 16 = true := by decide +kernel
private theorem mul_baseA1_check8 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 128 16 = true := by decide +kernel
private theorem mul_baseA1_check9 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 144 16 = true := by decide +kernel
private theorem mul_baseA1_check10 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 160 16 = true := by decide +kernel
private theorem mul_baseA1_check11 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 176 16 = true := by decide +kernel
private theorem mul_baseA1_check12 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 192 16 = true := by decide +kernel
private theorem mul_baseA1_check13 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 208 16 = true := by decide +kernel
private theorem mul_baseA1_check14 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 224 16 = true := by decide +kernel
private theorem mul_baseA1_check15 : checkRange (fun i => BinaryMatrix.listProduct y3[i]! x.toList 0 == baseA1[i]!) 240 8 = true := by decide +kernel
theorem mul_baseA1 : BinaryMatrix.decode 248 y3 * BinaryMatrix.decode 248 x = BinaryMatrix.decode 248 baseA1 := by
  apply checked_mul 248 y3 x baseA1 rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseA1_check0) (mul_baseA1_check1)) (checkRange_append (m := 16) (n := 16) (mul_baseA1_check2) (mul_baseA1_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseA1_check4) (mul_baseA1_check5)) (checkRange_append (m := 16) (n := 16) (mul_baseA1_check6) (mul_baseA1_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseA1_check8) (mul_baseA1_check9)) (checkRange_append (m := 16) (n := 16) (mul_baseA1_check10) (mul_baseA1_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_baseA1_check12) (mul_baseA1_check13)) (checkRange_append (m := 16) (n := 8) (mul_baseA1_check14) (mul_baseA1_check15))))
private theorem mul_baseA_check0 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 0 16 = true := by decide +kernel
private theorem mul_baseA_check1 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 16 16 = true := by decide +kernel
private theorem mul_baseA_check2 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 32 16 = true := by decide +kernel
private theorem mul_baseA_check3 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 48 16 = true := by decide +kernel
private theorem mul_baseA_check4 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 64 16 = true := by decide +kernel
private theorem mul_baseA_check5 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 80 16 = true := by decide +kernel
private theorem mul_baseA_check6 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 96 16 = true := by decide +kernel
private theorem mul_baseA_check7 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 112 16 = true := by decide +kernel
private theorem mul_baseA_check8 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 128 16 = true := by decide +kernel
private theorem mul_baseA_check9 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 144 16 = true := by decide +kernel
private theorem mul_baseA_check10 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 160 16 = true := by decide +kernel
private theorem mul_baseA_check11 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 176 16 = true := by decide +kernel
private theorem mul_baseA_check12 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 192 16 = true := by decide +kernel
private theorem mul_baseA_check13 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 208 16 = true := by decide +kernel
private theorem mul_baseA_check14 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 224 16 = true := by decide +kernel
private theorem mul_baseA_check15 : checkRange (fun i => BinaryMatrix.listProduct baseA1[i]! y2.toList 0 == baseA[i]!) 240 8 = true := by decide +kernel
theorem mul_baseA : BinaryMatrix.decode 248 baseA1 * BinaryMatrix.decode 248 y2 = BinaryMatrix.decode 248 baseA := by
  apply checked_mul 248 baseA1 y2 baseA rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseA_check0) (mul_baseA_check1)) (checkRange_append (m := 16) (n := 16) (mul_baseA_check2) (mul_baseA_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseA_check4) (mul_baseA_check5)) (checkRange_append (m := 16) (n := 16) (mul_baseA_check6) (mul_baseA_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseA_check8) (mul_baseA_check9)) (checkRange_append (m := 16) (n := 16) (mul_baseA_check10) (mul_baseA_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_baseA_check12) (mul_baseA_check13)) (checkRange_append (m := 16) (n := 8) (mul_baseA_check14) (mul_baseA_check15))))
private theorem mul_baseA2_check0 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 0 16 = true := by decide +kernel
private theorem mul_baseA2_check1 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 16 16 = true := by decide +kernel
private theorem mul_baseA2_check2 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 32 16 = true := by decide +kernel
private theorem mul_baseA2_check3 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 48 16 = true := by decide +kernel
private theorem mul_baseA2_check4 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 64 16 = true := by decide +kernel
private theorem mul_baseA2_check5 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 80 16 = true := by decide +kernel
private theorem mul_baseA2_check6 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 96 16 = true := by decide +kernel
private theorem mul_baseA2_check7 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 112 16 = true := by decide +kernel
private theorem mul_baseA2_check8 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 128 16 = true := by decide +kernel
private theorem mul_baseA2_check9 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 144 16 = true := by decide +kernel
private theorem mul_baseA2_check10 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 160 16 = true := by decide +kernel
private theorem mul_baseA2_check11 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 176 16 = true := by decide +kernel
private theorem mul_baseA2_check12 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 192 16 = true := by decide +kernel
private theorem mul_baseA2_check13 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 208 16 = true := by decide +kernel
private theorem mul_baseA2_check14 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 224 16 = true := by decide +kernel
private theorem mul_baseA2_check15 : checkRange (fun i => BinaryMatrix.listProduct baseA[i]! baseA.toList 0 == baseA2[i]!) 240 8 = true := by decide +kernel
theorem mul_baseA2 : BinaryMatrix.decode 248 baseA * BinaryMatrix.decode 248 baseA = BinaryMatrix.decode 248 baseA2 := by
  apply checked_mul 248 baseA baseA baseA2 rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseA2_check0) (mul_baseA2_check1)) (checkRange_append (m := 16) (n := 16) (mul_baseA2_check2) (mul_baseA2_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseA2_check4) (mul_baseA2_check5)) (checkRange_append (m := 16) (n := 16) (mul_baseA2_check6) (mul_baseA2_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseA2_check8) (mul_baseA2_check9)) (checkRange_append (m := 16) (n := 16) (mul_baseA2_check10) (mul_baseA2_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_baseA2_check12) (mul_baseA2_check13)) (checkRange_append (m := 16) (n := 8) (mul_baseA2_check14) (mul_baseA2_check15))))
private theorem mul_baseA3_check0 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 0 16 = true := by decide +kernel
private theorem mul_baseA3_check1 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 16 16 = true := by decide +kernel
private theorem mul_baseA3_check2 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 32 16 = true := by decide +kernel
private theorem mul_baseA3_check3 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 48 16 = true := by decide +kernel
private theorem mul_baseA3_check4 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 64 16 = true := by decide +kernel
private theorem mul_baseA3_check5 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 80 16 = true := by decide +kernel
private theorem mul_baseA3_check6 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 96 16 = true := by decide +kernel
private theorem mul_baseA3_check7 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 112 16 = true := by decide +kernel
private theorem mul_baseA3_check8 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 128 16 = true := by decide +kernel
private theorem mul_baseA3_check9 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 144 16 = true := by decide +kernel
private theorem mul_baseA3_check10 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 160 16 = true := by decide +kernel
private theorem mul_baseA3_check11 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 176 16 = true := by decide +kernel
private theorem mul_baseA3_check12 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 192 16 = true := by decide +kernel
private theorem mul_baseA3_check13 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 208 16 = true := by decide +kernel
private theorem mul_baseA3_check14 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 224 16 = true := by decide +kernel
private theorem mul_baseA3_check15 : checkRange (fun i => BinaryMatrix.listProduct baseA2[i]! baseA.toList 0 == baseA3[i]!) 240 8 = true := by decide +kernel
theorem mul_baseA3 : BinaryMatrix.decode 248 baseA2 * BinaryMatrix.decode 248 baseA = BinaryMatrix.decode 248 baseA3 := by
  apply checked_mul 248 baseA2 baseA baseA3 rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseA3_check0) (mul_baseA3_check1)) (checkRange_append (m := 16) (n := 16) (mul_baseA3_check2) (mul_baseA3_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseA3_check4) (mul_baseA3_check5)) (checkRange_append (m := 16) (n := 16) (mul_baseA3_check6) (mul_baseA3_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_baseA3_check8) (mul_baseA3_check9)) (checkRange_append (m := 16) (n := 16) (mul_baseA3_check10) (mul_baseA3_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_baseA3_check12) (mul_baseA3_check13)) (checkRange_append (m := 16) (n := 8) (mul_baseA3_check14) (mul_baseA3_check15))))
private theorem mul_a_check0 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 0 16 = true := by decide +kernel
private theorem mul_a_check1 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 16 16 = true := by decide +kernel
private theorem mul_a_check2 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 32 16 = true := by decide +kernel
private theorem mul_a_check3 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 48 16 = true := by decide +kernel
private theorem mul_a_check4 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 64 16 = true := by decide +kernel
private theorem mul_a_check5 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 80 16 = true := by decide +kernel
private theorem mul_a_check6 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 96 16 = true := by decide +kernel
private theorem mul_a_check7 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 112 16 = true := by decide +kernel
private theorem mul_a_check8 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 128 16 = true := by decide +kernel
private theorem mul_a_check9 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 144 16 = true := by decide +kernel
private theorem mul_a_check10 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 160 16 = true := by decide +kernel
private theorem mul_a_check11 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 176 16 = true := by decide +kernel
private theorem mul_a_check12 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 192 16 = true := by decide +kernel
private theorem mul_a_check13 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 208 16 = true := by decide +kernel
private theorem mul_a_check14 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 224 16 = true := by decide +kernel
private theorem mul_a_check15 : checkRange (fun i => BinaryMatrix.listProduct baseA3[i]! baseA3.toList 0 == a[i]!) 240 8 = true := by decide +kernel
theorem mul_a : BinaryMatrix.decode 248 baseA3 * BinaryMatrix.decode 248 baseA3 = BinaryMatrix.decode 248 a := by
  apply checked_mul 248 baseA3 baseA3 a rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_a_check0) (mul_a_check1)) (checkRange_append (m := 16) (n := 16) (mul_a_check2) (mul_a_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_a_check4) (mul_a_check5)) (checkRange_append (m := 16) (n := 16) (mul_a_check6) (mul_a_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (mul_a_check8) (mul_a_check9)) (checkRange_append (m := 16) (n := 16) (mul_a_check10) (mul_a_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (mul_a_check12) (mul_a_check13)) (checkRange_append (m := 16) (n := 8) (mul_a_check14) (mul_a_check15))))
theorem witness_y2 : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 y2 := witness_mul witness_y witness_y mul_y2
theorem witness_y3 : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 y3 := witness_mul witness_y2 witness_y mul_y3
theorem witness_xy : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 xy := witness_mul witness_x witness_y mul_xy
theorem witness_baseA1 : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 baseA1 := witness_mul witness_y3 witness_x mul_baseA1
theorem witness_baseA : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 baseA := witness_mul witness_baseA1 witness_y2 mul_baseA
theorem witness_baseA2 : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 baseA2 := witness_mul witness_baseA witness_baseA mul_baseA2
theorem witness_baseA3 : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 baseA3 := witness_mul witness_baseA2 witness_baseA mul_baseA3
theorem witness_a : ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 a := witness_mul witness_baseA3 witness_baseA3 mul_a
end Thompson.TwoRank.Matrices

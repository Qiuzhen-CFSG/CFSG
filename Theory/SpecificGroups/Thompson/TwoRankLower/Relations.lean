module
public import Theory.SpecificGroups.Thompson.TwoRankLower.Data
/-! Checked square and commutator products for the Thompson elementary eight. -/
public section
namespace Thompson.TwoRank.Matrices
open InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
set_option Elab.async false
private theorem rel_aa_check0 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 0 16 = true := by decide +kernel
private theorem rel_aa_check1 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 16 16 = true := by decide +kernel
private theorem rel_aa_check2 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 32 16 = true := by decide +kernel
private theorem rel_aa_check3 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 48 16 = true := by decide +kernel
private theorem rel_aa_check4 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 64 16 = true := by decide +kernel
private theorem rel_aa_check5 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 80 16 = true := by decide +kernel
private theorem rel_aa_check6 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 96 16 = true := by decide +kernel
private theorem rel_aa_check7 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 112 16 = true := by decide +kernel
private theorem rel_aa_check8 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 128 16 = true := by decide +kernel
private theorem rel_aa_check9 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 144 16 = true := by decide +kernel
private theorem rel_aa_check10 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 160 16 = true := by decide +kernel
private theorem rel_aa_check11 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 176 16 = true := by decide +kernel
private theorem rel_aa_check12 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 192 16 = true := by decide +kernel
private theorem rel_aa_check13 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 208 16 = true := by decide +kernel
private theorem rel_aa_check14 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 224 16 = true := by decide +kernel
private theorem rel_aa_check15 : checkRange (fun i => BinaryMatrix.listProduct a[i]! a.toList 0 == unit[i]!) 240 8 = true := by decide +kernel
theorem rel_aa : BinaryMatrix.decode 248 a * BinaryMatrix.decode 248 a = BinaryMatrix.decode 248 unit := by
  apply checked_mul 248 a a unit rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_aa_check0) (rel_aa_check1)) (checkRange_append (m := 16) (n := 16) (rel_aa_check2) (rel_aa_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_aa_check4) (rel_aa_check5)) (checkRange_append (m := 16) (n := 16) (rel_aa_check6) (rel_aa_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_aa_check8) (rel_aa_check9)) (checkRange_append (m := 16) (n := 16) (rel_aa_check10) (rel_aa_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (rel_aa_check12) (rel_aa_check13)) (checkRange_append (m := 16) (n := 8) (rel_aa_check14) (rel_aa_check15))))
private theorem rel_bb_check0 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 0 16 = true := by decide +kernel
private theorem rel_bb_check1 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 16 16 = true := by decide +kernel
private theorem rel_bb_check2 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 32 16 = true := by decide +kernel
private theorem rel_bb_check3 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 48 16 = true := by decide +kernel
private theorem rel_bb_check4 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 64 16 = true := by decide +kernel
private theorem rel_bb_check5 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 80 16 = true := by decide +kernel
private theorem rel_bb_check6 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 96 16 = true := by decide +kernel
private theorem rel_bb_check7 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 112 16 = true := by decide +kernel
private theorem rel_bb_check8 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 128 16 = true := by decide +kernel
private theorem rel_bb_check9 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 144 16 = true := by decide +kernel
private theorem rel_bb_check10 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 160 16 = true := by decide +kernel
private theorem rel_bb_check11 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 176 16 = true := by decide +kernel
private theorem rel_bb_check12 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 192 16 = true := by decide +kernel
private theorem rel_bb_check13 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 208 16 = true := by decide +kernel
private theorem rel_bb_check14 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 224 16 = true := by decide +kernel
private theorem rel_bb_check15 : checkRange (fun i => BinaryMatrix.listProduct b[i]! b.toList 0 == unit[i]!) 240 8 = true := by decide +kernel
theorem rel_bb : BinaryMatrix.decode 248 b * BinaryMatrix.decode 248 b = BinaryMatrix.decode 248 unit := by
  apply checked_mul 248 b b unit rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_bb_check0) (rel_bb_check1)) (checkRange_append (m := 16) (n := 16) (rel_bb_check2) (rel_bb_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_bb_check4) (rel_bb_check5)) (checkRange_append (m := 16) (n := 16) (rel_bb_check6) (rel_bb_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_bb_check8) (rel_bb_check9)) (checkRange_append (m := 16) (n := 16) (rel_bb_check10) (rel_bb_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (rel_bb_check12) (rel_bb_check13)) (checkRange_append (m := 16) (n := 8) (rel_bb_check14) (rel_bb_check15))))
private theorem rel_cc_check0 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 0 16 = true := by decide +kernel
private theorem rel_cc_check1 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 16 16 = true := by decide +kernel
private theorem rel_cc_check2 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 32 16 = true := by decide +kernel
private theorem rel_cc_check3 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 48 16 = true := by decide +kernel
private theorem rel_cc_check4 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 64 16 = true := by decide +kernel
private theorem rel_cc_check5 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 80 16 = true := by decide +kernel
private theorem rel_cc_check6 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 96 16 = true := by decide +kernel
private theorem rel_cc_check7 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 112 16 = true := by decide +kernel
private theorem rel_cc_check8 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 128 16 = true := by decide +kernel
private theorem rel_cc_check9 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 144 16 = true := by decide +kernel
private theorem rel_cc_check10 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 160 16 = true := by decide +kernel
private theorem rel_cc_check11 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 176 16 = true := by decide +kernel
private theorem rel_cc_check12 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 192 16 = true := by decide +kernel
private theorem rel_cc_check13 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 208 16 = true := by decide +kernel
private theorem rel_cc_check14 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 224 16 = true := by decide +kernel
private theorem rel_cc_check15 : checkRange (fun i => BinaryMatrix.listProduct c[i]! c.toList 0 == unit[i]!) 240 8 = true := by decide +kernel
theorem rel_cc : BinaryMatrix.decode 248 c * BinaryMatrix.decode 248 c = BinaryMatrix.decode 248 unit := by
  apply checked_mul 248 c c unit rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_cc_check0) (rel_cc_check1)) (checkRange_append (m := 16) (n := 16) (rel_cc_check2) (rel_cc_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_cc_check4) (rel_cc_check5)) (checkRange_append (m := 16) (n := 16) (rel_cc_check6) (rel_cc_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_cc_check8) (rel_cc_check9)) (checkRange_append (m := 16) (n := 16) (rel_cc_check10) (rel_cc_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (rel_cc_check12) (rel_cc_check13)) (checkRange_append (m := 16) (n := 8) (rel_cc_check14) (rel_cc_check15))))
private theorem rel_ab_check0 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 0 16 = true := by decide +kernel
private theorem rel_ab_check1 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 16 16 = true := by decide +kernel
private theorem rel_ab_check2 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 32 16 = true := by decide +kernel
private theorem rel_ab_check3 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 48 16 = true := by decide +kernel
private theorem rel_ab_check4 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 64 16 = true := by decide +kernel
private theorem rel_ab_check5 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 80 16 = true := by decide +kernel
private theorem rel_ab_check6 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 96 16 = true := by decide +kernel
private theorem rel_ab_check7 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 112 16 = true := by decide +kernel
private theorem rel_ab_check8 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 128 16 = true := by decide +kernel
private theorem rel_ab_check9 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 144 16 = true := by decide +kernel
private theorem rel_ab_check10 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 160 16 = true := by decide +kernel
private theorem rel_ab_check11 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 176 16 = true := by decide +kernel
private theorem rel_ab_check12 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 192 16 = true := by decide +kernel
private theorem rel_ab_check13 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 208 16 = true := by decide +kernel
private theorem rel_ab_check14 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 224 16 = true := by decide +kernel
private theorem rel_ab_check15 : checkRange (fun i => BinaryMatrix.listProduct a[i]! b.toList 0 == ab[i]!) 240 8 = true := by decide +kernel
theorem rel_ab : BinaryMatrix.decode 248 a * BinaryMatrix.decode 248 b = BinaryMatrix.decode 248 ab := by
  apply checked_mul 248 a b ab rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_ab_check0) (rel_ab_check1)) (checkRange_append (m := 16) (n := 16) (rel_ab_check2) (rel_ab_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_ab_check4) (rel_ab_check5)) (checkRange_append (m := 16) (n := 16) (rel_ab_check6) (rel_ab_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_ab_check8) (rel_ab_check9)) (checkRange_append (m := 16) (n := 16) (rel_ab_check10) (rel_ab_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (rel_ab_check12) (rel_ab_check13)) (checkRange_append (m := 16) (n := 8) (rel_ab_check14) (rel_ab_check15))))
private theorem rel_ba_check0 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 0 16 = true := by decide +kernel
private theorem rel_ba_check1 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 16 16 = true := by decide +kernel
private theorem rel_ba_check2 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 32 16 = true := by decide +kernel
private theorem rel_ba_check3 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 48 16 = true := by decide +kernel
private theorem rel_ba_check4 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 64 16 = true := by decide +kernel
private theorem rel_ba_check5 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 80 16 = true := by decide +kernel
private theorem rel_ba_check6 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 96 16 = true := by decide +kernel
private theorem rel_ba_check7 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 112 16 = true := by decide +kernel
private theorem rel_ba_check8 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 128 16 = true := by decide +kernel
private theorem rel_ba_check9 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 144 16 = true := by decide +kernel
private theorem rel_ba_check10 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 160 16 = true := by decide +kernel
private theorem rel_ba_check11 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 176 16 = true := by decide +kernel
private theorem rel_ba_check12 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 192 16 = true := by decide +kernel
private theorem rel_ba_check13 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 208 16 = true := by decide +kernel
private theorem rel_ba_check14 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 224 16 = true := by decide +kernel
private theorem rel_ba_check15 : checkRange (fun i => BinaryMatrix.listProduct b[i]! a.toList 0 == ab[i]!) 240 8 = true := by decide +kernel
theorem rel_ba : BinaryMatrix.decode 248 b * BinaryMatrix.decode 248 a = BinaryMatrix.decode 248 ab := by
  apply checked_mul 248 b a ab rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_ba_check0) (rel_ba_check1)) (checkRange_append (m := 16) (n := 16) (rel_ba_check2) (rel_ba_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_ba_check4) (rel_ba_check5)) (checkRange_append (m := 16) (n := 16) (rel_ba_check6) (rel_ba_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_ba_check8) (rel_ba_check9)) (checkRange_append (m := 16) (n := 16) (rel_ba_check10) (rel_ba_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (rel_ba_check12) (rel_ba_check13)) (checkRange_append (m := 16) (n := 8) (rel_ba_check14) (rel_ba_check15))))
private theorem rel_ac_check0 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 0 16 = true := by decide +kernel
private theorem rel_ac_check1 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 16 16 = true := by decide +kernel
private theorem rel_ac_check2 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 32 16 = true := by decide +kernel
private theorem rel_ac_check3 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 48 16 = true := by decide +kernel
private theorem rel_ac_check4 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 64 16 = true := by decide +kernel
private theorem rel_ac_check5 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 80 16 = true := by decide +kernel
private theorem rel_ac_check6 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 96 16 = true := by decide +kernel
private theorem rel_ac_check7 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 112 16 = true := by decide +kernel
private theorem rel_ac_check8 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 128 16 = true := by decide +kernel
private theorem rel_ac_check9 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 144 16 = true := by decide +kernel
private theorem rel_ac_check10 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 160 16 = true := by decide +kernel
private theorem rel_ac_check11 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 176 16 = true := by decide +kernel
private theorem rel_ac_check12 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 192 16 = true := by decide +kernel
private theorem rel_ac_check13 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 208 16 = true := by decide +kernel
private theorem rel_ac_check14 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 224 16 = true := by decide +kernel
private theorem rel_ac_check15 : checkRange (fun i => BinaryMatrix.listProduct a[i]! c.toList 0 == ac[i]!) 240 8 = true := by decide +kernel
theorem rel_ac : BinaryMatrix.decode 248 a * BinaryMatrix.decode 248 c = BinaryMatrix.decode 248 ac := by
  apply checked_mul 248 a c ac rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_ac_check0) (rel_ac_check1)) (checkRange_append (m := 16) (n := 16) (rel_ac_check2) (rel_ac_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_ac_check4) (rel_ac_check5)) (checkRange_append (m := 16) (n := 16) (rel_ac_check6) (rel_ac_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_ac_check8) (rel_ac_check9)) (checkRange_append (m := 16) (n := 16) (rel_ac_check10) (rel_ac_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (rel_ac_check12) (rel_ac_check13)) (checkRange_append (m := 16) (n := 8) (rel_ac_check14) (rel_ac_check15))))
private theorem rel_ca_check0 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 0 16 = true := by decide +kernel
private theorem rel_ca_check1 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 16 16 = true := by decide +kernel
private theorem rel_ca_check2 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 32 16 = true := by decide +kernel
private theorem rel_ca_check3 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 48 16 = true := by decide +kernel
private theorem rel_ca_check4 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 64 16 = true := by decide +kernel
private theorem rel_ca_check5 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 80 16 = true := by decide +kernel
private theorem rel_ca_check6 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 96 16 = true := by decide +kernel
private theorem rel_ca_check7 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 112 16 = true := by decide +kernel
private theorem rel_ca_check8 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 128 16 = true := by decide +kernel
private theorem rel_ca_check9 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 144 16 = true := by decide +kernel
private theorem rel_ca_check10 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 160 16 = true := by decide +kernel
private theorem rel_ca_check11 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 176 16 = true := by decide +kernel
private theorem rel_ca_check12 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 192 16 = true := by decide +kernel
private theorem rel_ca_check13 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 208 16 = true := by decide +kernel
private theorem rel_ca_check14 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 224 16 = true := by decide +kernel
private theorem rel_ca_check15 : checkRange (fun i => BinaryMatrix.listProduct c[i]! a.toList 0 == ac[i]!) 240 8 = true := by decide +kernel
theorem rel_ca : BinaryMatrix.decode 248 c * BinaryMatrix.decode 248 a = BinaryMatrix.decode 248 ac := by
  apply checked_mul 248 c a ac rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_ca_check0) (rel_ca_check1)) (checkRange_append (m := 16) (n := 16) (rel_ca_check2) (rel_ca_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_ca_check4) (rel_ca_check5)) (checkRange_append (m := 16) (n := 16) (rel_ca_check6) (rel_ca_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_ca_check8) (rel_ca_check9)) (checkRange_append (m := 16) (n := 16) (rel_ca_check10) (rel_ca_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (rel_ca_check12) (rel_ca_check13)) (checkRange_append (m := 16) (n := 8) (rel_ca_check14) (rel_ca_check15))))
private theorem rel_bc_check0 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 0 16 = true := by decide +kernel
private theorem rel_bc_check1 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 16 16 = true := by decide +kernel
private theorem rel_bc_check2 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 32 16 = true := by decide +kernel
private theorem rel_bc_check3 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 48 16 = true := by decide +kernel
private theorem rel_bc_check4 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 64 16 = true := by decide +kernel
private theorem rel_bc_check5 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 80 16 = true := by decide +kernel
private theorem rel_bc_check6 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 96 16 = true := by decide +kernel
private theorem rel_bc_check7 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 112 16 = true := by decide +kernel
private theorem rel_bc_check8 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 128 16 = true := by decide +kernel
private theorem rel_bc_check9 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 144 16 = true := by decide +kernel
private theorem rel_bc_check10 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 160 16 = true := by decide +kernel
private theorem rel_bc_check11 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 176 16 = true := by decide +kernel
private theorem rel_bc_check12 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 192 16 = true := by decide +kernel
private theorem rel_bc_check13 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 208 16 = true := by decide +kernel
private theorem rel_bc_check14 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 224 16 = true := by decide +kernel
private theorem rel_bc_check15 : checkRange (fun i => BinaryMatrix.listProduct b[i]! c.toList 0 == bc[i]!) 240 8 = true := by decide +kernel
theorem rel_bc : BinaryMatrix.decode 248 b * BinaryMatrix.decode 248 c = BinaryMatrix.decode 248 bc := by
  apply checked_mul 248 b c bc rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_bc_check0) (rel_bc_check1)) (checkRange_append (m := 16) (n := 16) (rel_bc_check2) (rel_bc_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_bc_check4) (rel_bc_check5)) (checkRange_append (m := 16) (n := 16) (rel_bc_check6) (rel_bc_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_bc_check8) (rel_bc_check9)) (checkRange_append (m := 16) (n := 16) (rel_bc_check10) (rel_bc_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (rel_bc_check12) (rel_bc_check13)) (checkRange_append (m := 16) (n := 8) (rel_bc_check14) (rel_bc_check15))))
private theorem rel_cb_check0 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 0 16 = true := by decide +kernel
private theorem rel_cb_check1 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 16 16 = true := by decide +kernel
private theorem rel_cb_check2 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 32 16 = true := by decide +kernel
private theorem rel_cb_check3 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 48 16 = true := by decide +kernel
private theorem rel_cb_check4 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 64 16 = true := by decide +kernel
private theorem rel_cb_check5 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 80 16 = true := by decide +kernel
private theorem rel_cb_check6 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 96 16 = true := by decide +kernel
private theorem rel_cb_check7 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 112 16 = true := by decide +kernel
private theorem rel_cb_check8 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 128 16 = true := by decide +kernel
private theorem rel_cb_check9 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 144 16 = true := by decide +kernel
private theorem rel_cb_check10 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 160 16 = true := by decide +kernel
private theorem rel_cb_check11 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 176 16 = true := by decide +kernel
private theorem rel_cb_check12 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 192 16 = true := by decide +kernel
private theorem rel_cb_check13 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 208 16 = true := by decide +kernel
private theorem rel_cb_check14 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 224 16 = true := by decide +kernel
private theorem rel_cb_check15 : checkRange (fun i => BinaryMatrix.listProduct c[i]! b.toList 0 == bc[i]!) 240 8 = true := by decide +kernel
theorem rel_cb : BinaryMatrix.decode 248 c * BinaryMatrix.decode 248 b = BinaryMatrix.decode 248 bc := by
  apply checked_mul 248 c b bc rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_cb_check0) (rel_cb_check1)) (checkRange_append (m := 16) (n := 16) (rel_cb_check2) (rel_cb_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_cb_check4) (rel_cb_check5)) (checkRange_append (m := 16) (n := 16) (rel_cb_check6) (rel_cb_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_cb_check8) (rel_cb_check9)) (checkRange_append (m := 16) (n := 16) (rel_cb_check10) (rel_cb_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (rel_cb_check12) (rel_cb_check13)) (checkRange_append (m := 16) (n := 8) (rel_cb_check14) (rel_cb_check15))))
private theorem rel_abc_check0 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 0 16 = true := by decide +kernel
private theorem rel_abc_check1 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 16 16 = true := by decide +kernel
private theorem rel_abc_check2 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 32 16 = true := by decide +kernel
private theorem rel_abc_check3 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 48 16 = true := by decide +kernel
private theorem rel_abc_check4 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 64 16 = true := by decide +kernel
private theorem rel_abc_check5 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 80 16 = true := by decide +kernel
private theorem rel_abc_check6 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 96 16 = true := by decide +kernel
private theorem rel_abc_check7 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 112 16 = true := by decide +kernel
private theorem rel_abc_check8 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 128 16 = true := by decide +kernel
private theorem rel_abc_check9 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 144 16 = true := by decide +kernel
private theorem rel_abc_check10 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 160 16 = true := by decide +kernel
private theorem rel_abc_check11 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 176 16 = true := by decide +kernel
private theorem rel_abc_check12 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 192 16 = true := by decide +kernel
private theorem rel_abc_check13 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 208 16 = true := by decide +kernel
private theorem rel_abc_check14 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 224 16 = true := by decide +kernel
private theorem rel_abc_check15 : checkRange (fun i => BinaryMatrix.listProduct ab[i]! c.toList 0 == abc[i]!) 240 8 = true := by decide +kernel
theorem rel_abc : BinaryMatrix.decode 248 ab * BinaryMatrix.decode 248 c = BinaryMatrix.decode 248 abc := by
  apply checked_mul 248 ab c abc rfl
  exact checkRange_append (m := 128) (n := 120) (checkRange_append (m := 64) (n := 64) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_abc_check0) (rel_abc_check1)) (checkRange_append (m := 16) (n := 16) (rel_abc_check2) (rel_abc_check3))) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_abc_check4) (rel_abc_check5)) (checkRange_append (m := 16) (n := 16) (rel_abc_check6) (rel_abc_check7)))) (checkRange_append (m := 64) (n := 56) (checkRange_append (m := 32) (n := 32) (checkRange_append (m := 16) (n := 16) (rel_abc_check8) (rel_abc_check9)) (checkRange_append (m := 16) (n := 16) (rel_abc_check10) (rel_abc_check11))) (checkRange_append (m := 32) (n := 24) (checkRange_append (m := 16) (n := 16) (rel_abc_check12) (rel_abc_check13)) (checkRange_append (m := 16) (n := 8) (rel_abc_check14) (rel_abc_check15))))
theorem decode_unit : BinaryMatrix.decode 248 unit = 1 := by
  have h : ∀ i : Fin 248, unit[i.val]! = 2 ^ i.val := by decide +kernel
  ext i j
  change BinaryMatrix.bit unit[i.val]! j.val = _
  rw [h i]
  simp [BinaryMatrix.bit,Nat.testBit_two_pow,Matrix.one_apply,Fin.ext_iff]
end Thompson.TwoRank.Matrices

module
public import Theory.SpecificGroups.Lyons.TwoRankLower.First
/-! Checked word products for the actual Lyons elementary eight. See Data. -/
public section
namespace Lyons.TwoRank.Matrices
open Atlas111WordCertificate MatrixCheck
set_option Elab.async false
private theorem mul_baseB1_check0 : checkRange (fun j => digitsEq 111 (listProduct (x (Fin.ofNat 111 j)) y2List) (baseB1 (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem mul_baseB1_check1 : checkRange (fun j => digitsEq 111 (listProduct (x (Fin.ofNat 111 j)) y2List) (baseB1 (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem mul_baseB1_check2 : checkRange (fun j => digitsEq 111 (listProduct (x (Fin.ofNat 111 j)) y2List) (baseB1 (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem mul_baseB1_check3 : checkRange (fun j => digitsEq 111 (listProduct (x (Fin.ofNat 111 j)) y2List) (baseB1 (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem mul_baseB1_check4 : checkRange (fun j => digitsEq 111 (listProduct (x (Fin.ofNat 111 j)) y2List) (baseB1 (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem mul_baseB1_check5 : checkRange (fun j => digitsEq 111 (listProduct (x (Fin.ofNat 111 j)) y2List) (baseB1 (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem mul_baseB1_check6 : checkRange (fun j => digitsEq 111 (listProduct (x (Fin.ofNat 111 j)) y2List) (baseB1 (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem mul_baseB1 : decode x * decode y2 = decode baseB1 := by
  apply decode_mul_literal x y2 baseB1 y2List y2_list x_small y2_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (x (Fin.ofNat 111 j)) y2List) (baseB1 (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (mul_baseB1_check0) (checkRange_append (m := 16) (n := 16) (mul_baseB1_check1) (mul_baseB1_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (mul_baseB1_check3) (mul_baseB1_check4)) (checkRange_append (m := 16) (n := 15) (mul_baseB1_check5) (mul_baseB1_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem mul_baseB2_check0 : checkRange (fun j => digitsEq 111 (listProduct (baseB1 (Fin.ofNat 111 j)) xList) (baseB2 (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem mul_baseB2_check1 : checkRange (fun j => digitsEq 111 (listProduct (baseB1 (Fin.ofNat 111 j)) xList) (baseB2 (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem mul_baseB2_check2 : checkRange (fun j => digitsEq 111 (listProduct (baseB1 (Fin.ofNat 111 j)) xList) (baseB2 (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem mul_baseB2_check3 : checkRange (fun j => digitsEq 111 (listProduct (baseB1 (Fin.ofNat 111 j)) xList) (baseB2 (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem mul_baseB2_check4 : checkRange (fun j => digitsEq 111 (listProduct (baseB1 (Fin.ofNat 111 j)) xList) (baseB2 (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem mul_baseB2_check5 : checkRange (fun j => digitsEq 111 (listProduct (baseB1 (Fin.ofNat 111 j)) xList) (baseB2 (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem mul_baseB2_check6 : checkRange (fun j => digitsEq 111 (listProduct (baseB1 (Fin.ofNat 111 j)) xList) (baseB2 (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem mul_baseB2 : decode baseB1 * decode x = decode baseB2 := by
  apply decode_mul_literal baseB1 x baseB2 xList x_list baseB1_small x_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (baseB1 (Fin.ofNat 111 j)) xList) (baseB2 (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (mul_baseB2_check0) (checkRange_append (m := 16) (n := 16) (mul_baseB2_check1) (mul_baseB2_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (mul_baseB2_check3) (mul_baseB2_check4)) (checkRange_append (m := 16) (n := 15) (mul_baseB2_check5) (mul_baseB2_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem mul_baseB3_check0 : checkRange (fun j => digitsEq 111 (listProduct (baseB2 (Fin.ofNat 111 j)) yList) (baseB3 (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem mul_baseB3_check1 : checkRange (fun j => digitsEq 111 (listProduct (baseB2 (Fin.ofNat 111 j)) yList) (baseB3 (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem mul_baseB3_check2 : checkRange (fun j => digitsEq 111 (listProduct (baseB2 (Fin.ofNat 111 j)) yList) (baseB3 (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem mul_baseB3_check3 : checkRange (fun j => digitsEq 111 (listProduct (baseB2 (Fin.ofNat 111 j)) yList) (baseB3 (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem mul_baseB3_check4 : checkRange (fun j => digitsEq 111 (listProduct (baseB2 (Fin.ofNat 111 j)) yList) (baseB3 (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem mul_baseB3_check5 : checkRange (fun j => digitsEq 111 (listProduct (baseB2 (Fin.ofNat 111 j)) yList) (baseB3 (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem mul_baseB3_check6 : checkRange (fun j => digitsEq 111 (listProduct (baseB2 (Fin.ofNat 111 j)) yList) (baseB3 (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem mul_baseB3 : decode baseB2 * decode y = decode baseB3 := by
  apply decode_mul_literal baseB2 y baseB3 yList y_list baseB2_small y_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (baseB2 (Fin.ofNat 111 j)) yList) (baseB3 (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (mul_baseB3_check0) (checkRange_append (m := 16) (n := 16) (mul_baseB3_check1) (mul_baseB3_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (mul_baseB3_check3) (mul_baseB3_check4)) (checkRange_append (m := 16) (n := 15) (mul_baseB3_check5) (mul_baseB3_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem mul_baseB_check0 : checkRange (fun j => digitsEq 111 (listProduct (baseB3 (Fin.ofNat 111 j)) xList) (baseB (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem mul_baseB_check1 : checkRange (fun j => digitsEq 111 (listProduct (baseB3 (Fin.ofNat 111 j)) xList) (baseB (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem mul_baseB_check2 : checkRange (fun j => digitsEq 111 (listProduct (baseB3 (Fin.ofNat 111 j)) xList) (baseB (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem mul_baseB_check3 : checkRange (fun j => digitsEq 111 (listProduct (baseB3 (Fin.ofNat 111 j)) xList) (baseB (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem mul_baseB_check4 : checkRange (fun j => digitsEq 111 (listProduct (baseB3 (Fin.ofNat 111 j)) xList) (baseB (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem mul_baseB_check5 : checkRange (fun j => digitsEq 111 (listProduct (baseB3 (Fin.ofNat 111 j)) xList) (baseB (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem mul_baseB_check6 : checkRange (fun j => digitsEq 111 (listProduct (baseB3 (Fin.ofNat 111 j)) xList) (baseB (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem mul_baseB : decode baseB3 * decode x = decode baseB := by
  apply decode_mul_literal baseB3 x baseB xList x_list baseB3_small x_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (baseB3 (Fin.ofNat 111 j)) xList) (baseB (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (mul_baseB_check0) (checkRange_append (m := 16) (n := 16) (mul_baseB_check1) (mul_baseB_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (mul_baseB_check3) (mul_baseB_check4)) (checkRange_append (m := 16) (n := 15) (mul_baseB_check5) (mul_baseB_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem mul_baseB2pow_check0 : checkRange (fun j => digitsEq 111 (listProduct (baseB (Fin.ofNat 111 j)) baseBList) (baseB2pow (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem mul_baseB2pow_check1 : checkRange (fun j => digitsEq 111 (listProduct (baseB (Fin.ofNat 111 j)) baseBList) (baseB2pow (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem mul_baseB2pow_check2 : checkRange (fun j => digitsEq 111 (listProduct (baseB (Fin.ofNat 111 j)) baseBList) (baseB2pow (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem mul_baseB2pow_check3 : checkRange (fun j => digitsEq 111 (listProduct (baseB (Fin.ofNat 111 j)) baseBList) (baseB2pow (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem mul_baseB2pow_check4 : checkRange (fun j => digitsEq 111 (listProduct (baseB (Fin.ofNat 111 j)) baseBList) (baseB2pow (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem mul_baseB2pow_check5 : checkRange (fun j => digitsEq 111 (listProduct (baseB (Fin.ofNat 111 j)) baseBList) (baseB2pow (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem mul_baseB2pow_check6 : checkRange (fun j => digitsEq 111 (listProduct (baseB (Fin.ofNat 111 j)) baseBList) (baseB2pow (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem mul_baseB2pow : decode baseB * decode baseB = decode baseB2pow := by
  apply decode_mul_literal baseB baseB baseB2pow baseBList baseB_list baseB_small baseB_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (baseB (Fin.ofNat 111 j)) baseBList) (baseB2pow (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (mul_baseB2pow_check0) (checkRange_append (m := 16) (n := 16) (mul_baseB2pow_check1) (mul_baseB2pow_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (mul_baseB2pow_check3) (mul_baseB2pow_check4)) (checkRange_append (m := 16) (n := 15) (mul_baseB2pow_check5) (mul_baseB2pow_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem mul_b_check0 : checkRange (fun j => digitsEq 111 (listProduct (baseB2pow (Fin.ofNat 111 j)) baseBList) (b (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem mul_b_check1 : checkRange (fun j => digitsEq 111 (listProduct (baseB2pow (Fin.ofNat 111 j)) baseBList) (b (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem mul_b_check2 : checkRange (fun j => digitsEq 111 (listProduct (baseB2pow (Fin.ofNat 111 j)) baseBList) (b (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem mul_b_check3 : checkRange (fun j => digitsEq 111 (listProduct (baseB2pow (Fin.ofNat 111 j)) baseBList) (b (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem mul_b_check4 : checkRange (fun j => digitsEq 111 (listProduct (baseB2pow (Fin.ofNat 111 j)) baseBList) (b (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem mul_b_check5 : checkRange (fun j => digitsEq 111 (listProduct (baseB2pow (Fin.ofNat 111 j)) baseBList) (b (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem mul_b_check6 : checkRange (fun j => digitsEq 111 (listProduct (baseB2pow (Fin.ofNat 111 j)) baseBList) (b (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem mul_b : decode baseB2pow * decode baseB = decode b := by
  apply decode_mul_literal baseB2pow baseB b baseBList baseB_list baseB2pow_small baseB_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (baseB2pow (Fin.ofNat 111 j)) baseBList) (b (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (mul_b_check0) (checkRange_append (m := 16) (n := 16) (mul_b_check1) (mul_b_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (mul_b_check3) (mul_b_check4)) (checkRange_append (m := 16) (n := 15) (mul_b_check5) (mul_b_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
theorem witness_baseB1 : ∃ g : LyonsGroup, matrixRepresentation g = decode baseB1 := witness_mul witness_x witness_y2 mul_baseB1
theorem witness_baseB2 : ∃ g : LyonsGroup, matrixRepresentation g = decode baseB2 := witness_mul witness_baseB1 witness_x mul_baseB2
theorem witness_baseB3 : ∃ g : LyonsGroup, matrixRepresentation g = decode baseB3 := witness_mul witness_baseB2 witness_y mul_baseB3
theorem witness_baseB : ∃ g : LyonsGroup, matrixRepresentation g = decode baseB := witness_mul witness_baseB3 witness_x mul_baseB
theorem witness_baseB2pow : ∃ g : LyonsGroup, matrixRepresentation g = decode baseB2pow := witness_mul witness_baseB witness_baseB mul_baseB2pow
theorem witness_b : ∃ g : LyonsGroup, matrixRepresentation g = decode b := witness_mul witness_baseB2pow witness_baseB mul_b
end Lyons.TwoRank.Matrices

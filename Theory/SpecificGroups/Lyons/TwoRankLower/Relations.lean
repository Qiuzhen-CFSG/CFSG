module
public import Theory.SpecificGroups.Lyons.TwoRankLower.Data
/-! Checked square and commutator products for the actual Lyons elementary eight. -/
public section
namespace Lyons.TwoRank.Matrices
open Atlas111WordCertificate MatrixCheck
set_option Elab.async false
private theorem rel_aa_check0 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) aList) (unit (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem rel_aa_check1 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) aList) (unit (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem rel_aa_check2 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) aList) (unit (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem rel_aa_check3 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) aList) (unit (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem rel_aa_check4 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) aList) (unit (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem rel_aa_check5 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) aList) (unit (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem rel_aa_check6 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) aList) (unit (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem rel_aa : decode a * decode a = decode unit := by
  apply decode_mul_literal a a unit aList a_list a_small a_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) aList) (unit (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (rel_aa_check0) (checkRange_append (m := 16) (n := 16) (rel_aa_check1) (rel_aa_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (rel_aa_check3) (rel_aa_check4)) (checkRange_append (m := 16) (n := 15) (rel_aa_check5) (rel_aa_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem rel_bb_check0 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) bList) (unit (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem rel_bb_check1 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) bList) (unit (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem rel_bb_check2 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) bList) (unit (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem rel_bb_check3 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) bList) (unit (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem rel_bb_check4 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) bList) (unit (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem rel_bb_check5 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) bList) (unit (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem rel_bb_check6 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) bList) (unit (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem rel_bb : decode b * decode b = decode unit := by
  apply decode_mul_literal b b unit bList b_list b_small b_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) bList) (unit (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (rel_bb_check0) (checkRange_append (m := 16) (n := 16) (rel_bb_check1) (rel_bb_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (rel_bb_check3) (rel_bb_check4)) (checkRange_append (m := 16) (n := 15) (rel_bb_check5) (rel_bb_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem rel_tt_check0 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) tList) (unit (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem rel_tt_check1 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) tList) (unit (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem rel_tt_check2 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) tList) (unit (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem rel_tt_check3 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) tList) (unit (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem rel_tt_check4 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) tList) (unit (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem rel_tt_check5 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) tList) (unit (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem rel_tt_check6 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) tList) (unit (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem rel_tt : decode t * decode t = decode unit := by
  apply decode_mul_literal t t unit tList t_list t_small t_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) tList) (unit (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (rel_tt_check0) (checkRange_append (m := 16) (n := 16) (rel_tt_check1) (rel_tt_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (rel_tt_check3) (rel_tt_check4)) (checkRange_append (m := 16) (n := 15) (rel_tt_check5) (rel_tt_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem rel_ab_check0 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) bList) (ab (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem rel_ab_check1 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) bList) (ab (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem rel_ab_check2 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) bList) (ab (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem rel_ab_check3 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) bList) (ab (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem rel_ab_check4 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) bList) (ab (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem rel_ab_check5 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) bList) (ab (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem rel_ab_check6 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) bList) (ab (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem rel_ab : decode a * decode b = decode ab := by
  apply decode_mul_literal a b ab bList b_list a_small b_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) bList) (ab (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (rel_ab_check0) (checkRange_append (m := 16) (n := 16) (rel_ab_check1) (rel_ab_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (rel_ab_check3) (rel_ab_check4)) (checkRange_append (m := 16) (n := 15) (rel_ab_check5) (rel_ab_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem rel_ba_check0 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) aList) (ab (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem rel_ba_check1 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) aList) (ab (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem rel_ba_check2 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) aList) (ab (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem rel_ba_check3 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) aList) (ab (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem rel_ba_check4 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) aList) (ab (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem rel_ba_check5 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) aList) (ab (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem rel_ba_check6 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) aList) (ab (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem rel_ba : decode b * decode a = decode ab := by
  apply decode_mul_literal b a ab aList a_list b_small a_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) aList) (ab (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (rel_ba_check0) (checkRange_append (m := 16) (n := 16) (rel_ba_check1) (rel_ba_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (rel_ba_check3) (rel_ba_check4)) (checkRange_append (m := 16) (n := 15) (rel_ba_check5) (rel_ba_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem rel_at_check0 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) tList) (ac (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem rel_at_check1 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) tList) (ac (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem rel_at_check2 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) tList) (ac (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem rel_at_check3 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) tList) (ac (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem rel_at_check4 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) tList) (ac (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem rel_at_check5 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) tList) (ac (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem rel_at_check6 : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) tList) (ac (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem rel_at : decode a * decode t = decode ac := by
  apply decode_mul_literal a t ac tList t_list a_small t_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (a (Fin.ofNat 111 j)) tList) (ac (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (rel_at_check0) (checkRange_append (m := 16) (n := 16) (rel_at_check1) (rel_at_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (rel_at_check3) (rel_at_check4)) (checkRange_append (m := 16) (n := 15) (rel_at_check5) (rel_at_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem rel_ta_check0 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) aList) (ac (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem rel_ta_check1 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) aList) (ac (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem rel_ta_check2 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) aList) (ac (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem rel_ta_check3 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) aList) (ac (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem rel_ta_check4 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) aList) (ac (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem rel_ta_check5 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) aList) (ac (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem rel_ta_check6 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) aList) (ac (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem rel_ta : decode t * decode a = decode ac := by
  apply decode_mul_literal t a ac aList a_list t_small a_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) aList) (ac (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (rel_ta_check0) (checkRange_append (m := 16) (n := 16) (rel_ta_check1) (rel_ta_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (rel_ta_check3) (rel_ta_check4)) (checkRange_append (m := 16) (n := 15) (rel_ta_check5) (rel_ta_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem rel_bt_check0 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) tList) (bc (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem rel_bt_check1 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) tList) (bc (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem rel_bt_check2 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) tList) (bc (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem rel_bt_check3 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) tList) (bc (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem rel_bt_check4 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) tList) (bc (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem rel_bt_check5 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) tList) (bc (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem rel_bt_check6 : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) tList) (bc (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem rel_bt : decode b * decode t = decode bc := by
  apply decode_mul_literal b t bc tList t_list b_small t_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (b (Fin.ofNat 111 j)) tList) (bc (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (rel_bt_check0) (checkRange_append (m := 16) (n := 16) (rel_bt_check1) (rel_bt_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (rel_bt_check3) (rel_bt_check4)) (checkRange_append (m := 16) (n := 15) (rel_bt_check5) (rel_bt_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem rel_tb_check0 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) bList) (bc (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem rel_tb_check1 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) bList) (bc (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem rel_tb_check2 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) bList) (bc (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem rel_tb_check3 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) bList) (bc (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem rel_tb_check4 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) bList) (bc (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem rel_tb_check5 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) bList) (bc (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem rel_tb_check6 : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) bList) (bc (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem rel_tb : decode t * decode b = decode bc := by
  apply decode_mul_literal t b bc bList b_list t_small b_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (t (Fin.ofNat 111 j)) bList) (bc (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (rel_tb_check0) (checkRange_append (m := 16) (n := 16) (rel_tb_check1) (rel_tb_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (rel_tb_check3) (rel_tb_check4)) (checkRange_append (m := 16) (n := 15) (rel_tb_check5) (rel_tb_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem ab_small (i : Fin 111) : small 111 (ab i) = true := by
  have h : allRows (fun i => small 111 (ab i)) = true := by decide +kernel
  exact allRows_sound h i
private theorem rel_abt_check0 : checkRange (fun j => digitsEq 111 (listProduct (ab (Fin.ofNat 111 j)) tList) (abc (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem rel_abt_check1 : checkRange (fun j => digitsEq 111 (listProduct (ab (Fin.ofNat 111 j)) tList) (abc (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem rel_abt_check2 : checkRange (fun j => digitsEq 111 (listProduct (ab (Fin.ofNat 111 j)) tList) (abc (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem rel_abt_check3 : checkRange (fun j => digitsEq 111 (listProduct (ab (Fin.ofNat 111 j)) tList) (abc (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem rel_abt_check4 : checkRange (fun j => digitsEq 111 (listProduct (ab (Fin.ofNat 111 j)) tList) (abc (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem rel_abt_check5 : checkRange (fun j => digitsEq 111 (listProduct (ab (Fin.ofNat 111 j)) tList) (abc (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem rel_abt_check6 : checkRange (fun j => digitsEq 111 (listProduct (ab (Fin.ofNat 111 j)) tList) (abc (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem rel_abt : decode ab * decode t = decode abc := by
  apply decode_mul_literal ab t abc tList t_list ab_small t_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (ab (Fin.ofNat 111 j)) tList) (abc (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (rel_abt_check0) (checkRange_append (m := 16) (n := 16) (rel_abt_check1) (rel_abt_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (rel_abt_check3) (rel_abt_check4)) (checkRange_append (m := 16) (n := 15) (rel_abt_check5) (rel_abt_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
end Lyons.TwoRank.Matrices

module
public import Theory.SpecificGroups.Lyons.TwoRankLower.Data
/-! Checked word products for the actual Lyons elementary eight. See Data. -/
public section
namespace Lyons.TwoRank.Matrices
open Atlas111WordCertificate MatrixCheck
set_option Elab.async false
theorem witness_mul {a b c : Rows}
    (ha : ∃ g : LyonsGroup, matrixRepresentation g = decode a)
    (hb : ∃ g : LyonsGroup, matrixRepresentation g = decode b)
    (hm : decode a * decode b = decode c) :
    ∃ g : LyonsGroup, matrixRepresentation g = decode c := by
  obtain ⟨g,hg⟩ := ha
  obtain ⟨f,hf⟩ := hb
  exact ⟨g*f,by rw [map_mul,hg,hf,hm]⟩
theorem witness_x : ∃ g : LyonsGroup, matrixRepresentation g = decode x :=
  ⟨SimplicityCertificate.involutionLocalA,SimplicityCertificate.LocalCommutant.Words.image_localA⟩
theorem witness_y : ∃ g : LyonsGroup, matrixRepresentation g = decode y :=
  ⟨SimplicityCertificate.involutionLocalB,SimplicityCertificate.LocalCommutant.Words.image_localB⟩
theorem witness_t : ∃ g : LyonsGroup, matrixRepresentation g = decode t :=
  ⟨SimplicityCertificate.involutionLocalT,SimplicityCertificate.LocalCommutant.Words.image_t⟩
theorem witness_x2 : ∃ g : LyonsGroup, matrixRepresentation g = decode x2 := by
  refine ⟨SimplicityCertificate.involutionLocalA^2,?_⟩
  rw [map_pow,SimplicityCertificate.LocalCommutant.Words.image_localA,pow_two,mul_ab2]
  rfl
private theorem mul_y2_check0 : checkRange (fun j => digitsEq 111 (listProduct (y (Fin.ofNat 111 j)) yList) (y2 (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem mul_y2_check1 : checkRange (fun j => digitsEq 111 (listProduct (y (Fin.ofNat 111 j)) yList) (y2 (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem mul_y2_check2 : checkRange (fun j => digitsEq 111 (listProduct (y (Fin.ofNat 111 j)) yList) (y2 (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem mul_y2_check3 : checkRange (fun j => digitsEq 111 (listProduct (y (Fin.ofNat 111 j)) yList) (y2 (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem mul_y2_check4 : checkRange (fun j => digitsEq 111 (listProduct (y (Fin.ofNat 111 j)) yList) (y2 (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem mul_y2_check5 : checkRange (fun j => digitsEq 111 (listProduct (y (Fin.ofNat 111 j)) yList) (y2 (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem mul_y2_check6 : checkRange (fun j => digitsEq 111 (listProduct (y (Fin.ofNat 111 j)) yList) (y2 (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem mul_y2 : decode y * decode y = decode y2 := by
  apply decode_mul_literal y y y2 yList y_list y_small y_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (y (Fin.ofNat 111 j)) yList) (y2 (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (mul_y2_check0) (checkRange_append (m := 16) (n := 16) (mul_y2_check1) (mul_y2_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (mul_y2_check3) (mul_y2_check4)) (checkRange_append (m := 16) (n := 15) (mul_y2_check5) (mul_y2_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem mul_y4_check0 : checkRange (fun j => digitsEq 111 (listProduct (y2 (Fin.ofNat 111 j)) y2List) (y4 (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem mul_y4_check1 : checkRange (fun j => digitsEq 111 (listProduct (y2 (Fin.ofNat 111 j)) y2List) (y4 (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem mul_y4_check2 : checkRange (fun j => digitsEq 111 (listProduct (y2 (Fin.ofNat 111 j)) y2List) (y4 (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem mul_y4_check3 : checkRange (fun j => digitsEq 111 (listProduct (y2 (Fin.ofNat 111 j)) y2List) (y4 (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem mul_y4_check4 : checkRange (fun j => digitsEq 111 (listProduct (y2 (Fin.ofNat 111 j)) y2List) (y4 (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem mul_y4_check5 : checkRange (fun j => digitsEq 111 (listProduct (y2 (Fin.ofNat 111 j)) y2List) (y4 (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem mul_y4_check6 : checkRange (fun j => digitsEq 111 (listProduct (y2 (Fin.ofNat 111 j)) y2List) (y4 (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem mul_y4 : decode y2 * decode y2 = decode y4 := by
  apply decode_mul_literal y2 y2 y4 y2List y2_list y2_small y2_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (y2 (Fin.ofNat 111 j)) y2List) (y4 (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (mul_y4_check0) (checkRange_append (m := 16) (n := 16) (mul_y4_check1) (mul_y4_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (mul_y4_check3) (mul_y4_check4)) (checkRange_append (m := 16) (n := 15) (mul_y4_check5) (mul_y4_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem mul_baseA_check0 : checkRange (fun j => digitsEq 111 (listProduct (x2 (Fin.ofNat 111 j)) y4List) (baseA (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem mul_baseA_check1 : checkRange (fun j => digitsEq 111 (listProduct (x2 (Fin.ofNat 111 j)) y4List) (baseA (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem mul_baseA_check2 : checkRange (fun j => digitsEq 111 (listProduct (x2 (Fin.ofNat 111 j)) y4List) (baseA (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem mul_baseA_check3 : checkRange (fun j => digitsEq 111 (listProduct (x2 (Fin.ofNat 111 j)) y4List) (baseA (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem mul_baseA_check4 : checkRange (fun j => digitsEq 111 (listProduct (x2 (Fin.ofNat 111 j)) y4List) (baseA (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem mul_baseA_check5 : checkRange (fun j => digitsEq 111 (listProduct (x2 (Fin.ofNat 111 j)) y4List) (baseA (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem mul_baseA_check6 : checkRange (fun j => digitsEq 111 (listProduct (x2 (Fin.ofNat 111 j)) y4List) (baseA (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem mul_baseA : decode x2 * decode y4 = decode baseA := by
  apply decode_mul_literal x2 y4 baseA y4List y4_list x2_small y4_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (x2 (Fin.ofNat 111 j)) y4List) (baseA (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (mul_baseA_check0) (checkRange_append (m := 16) (n := 16) (mul_baseA_check1) (mul_baseA_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (mul_baseA_check3) (mul_baseA_check4)) (checkRange_append (m := 16) (n := 15) (mul_baseA_check5) (mul_baseA_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem mul_baseA2_check0 : checkRange (fun j => digitsEq 111 (listProduct (baseA (Fin.ofNat 111 j)) baseAList) (baseA2 (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem mul_baseA2_check1 : checkRange (fun j => digitsEq 111 (listProduct (baseA (Fin.ofNat 111 j)) baseAList) (baseA2 (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem mul_baseA2_check2 : checkRange (fun j => digitsEq 111 (listProduct (baseA (Fin.ofNat 111 j)) baseAList) (baseA2 (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem mul_baseA2_check3 : checkRange (fun j => digitsEq 111 (listProduct (baseA (Fin.ofNat 111 j)) baseAList) (baseA2 (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem mul_baseA2_check4 : checkRange (fun j => digitsEq 111 (listProduct (baseA (Fin.ofNat 111 j)) baseAList) (baseA2 (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem mul_baseA2_check5 : checkRange (fun j => digitsEq 111 (listProduct (baseA (Fin.ofNat 111 j)) baseAList) (baseA2 (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem mul_baseA2_check6 : checkRange (fun j => digitsEq 111 (listProduct (baseA (Fin.ofNat 111 j)) baseAList) (baseA2 (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem mul_baseA2 : decode baseA * decode baseA = decode baseA2 := by
  apply decode_mul_literal baseA baseA baseA2 baseAList baseA_list baseA_small baseA_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (baseA (Fin.ofNat 111 j)) baseAList) (baseA2 (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (mul_baseA2_check0) (checkRange_append (m := 16) (n := 16) (mul_baseA2_check1) (mul_baseA2_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (mul_baseA2_check3) (mul_baseA2_check4)) (checkRange_append (m := 16) (n := 15) (mul_baseA2_check5) (mul_baseA2_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
private theorem mul_a_check0 : checkRange (fun j => digitsEq 111 (listProduct (baseA2 (Fin.ofNat 111 j)) baseA2List) (a (Fin.ofNat 111 j))) 0 16 = true := by decide +kernel
private theorem mul_a_check1 : checkRange (fun j => digitsEq 111 (listProduct (baseA2 (Fin.ofNat 111 j)) baseA2List) (a (Fin.ofNat 111 j))) 16 16 = true := by decide +kernel
private theorem mul_a_check2 : checkRange (fun j => digitsEq 111 (listProduct (baseA2 (Fin.ofNat 111 j)) baseA2List) (a (Fin.ofNat 111 j))) 32 16 = true := by decide +kernel
private theorem mul_a_check3 : checkRange (fun j => digitsEq 111 (listProduct (baseA2 (Fin.ofNat 111 j)) baseA2List) (a (Fin.ofNat 111 j))) 48 16 = true := by decide +kernel
private theorem mul_a_check4 : checkRange (fun j => digitsEq 111 (listProduct (baseA2 (Fin.ofNat 111 j)) baseA2List) (a (Fin.ofNat 111 j))) 64 16 = true := by decide +kernel
private theorem mul_a_check5 : checkRange (fun j => digitsEq 111 (listProduct (baseA2 (Fin.ofNat 111 j)) baseA2List) (a (Fin.ofNat 111 j))) 80 16 = true := by decide +kernel
private theorem mul_a_check6 : checkRange (fun j => digitsEq 111 (listProduct (baseA2 (Fin.ofNat 111 j)) baseA2List) (a (Fin.ofNat 111 j))) 96 15 = true := by decide +kernel
theorem mul_a : decode baseA2 * decode baseA2 = decode a := by
  apply decode_mul_literal baseA2 baseA2 a baseA2List baseA2_list baseA2_small baseA2_small
  intro i
  have h : checkRange (fun j => digitsEq 111 (listProduct (baseA2 (Fin.ofNat 111 j)) baseA2List) (a (Fin.ofNat 111 j))) 0 111 = true := checkRange_append (m := 48) (n := 63) (checkRange_append (m := 16) (n := 32) (mul_a_check0) (checkRange_append (m := 16) (n := 16) (mul_a_check1) (mul_a_check2))) (checkRange_append (m := 32) (n := 31) (checkRange_append (m := 16) (n := 16) (mul_a_check3) (mul_a_check4)) (checkRange_append (m := 16) (n := 15) (mul_a_check5) (mul_a_check6)))
  have hi := ((checkRange_spec _ _ _).mp h) i.val i.isLt
  have he : Fin.ofNat 111 i.val = i := by ext; exact Nat.mod_eq_of_lt i.isLt
  simpa only [Nat.zero_add,he] using hi
theorem witness_y2 : ∃ g : LyonsGroup, matrixRepresentation g = decode y2 := witness_mul witness_y witness_y mul_y2
theorem witness_y4 : ∃ g : LyonsGroup, matrixRepresentation g = decode y4 := witness_mul witness_y2 witness_y2 mul_y4
theorem witness_baseA : ∃ g : LyonsGroup, matrixRepresentation g = decode baseA := witness_mul witness_x2 witness_y4 mul_baseA
theorem witness_baseA2 : ∃ g : LyonsGroup, matrixRepresentation g = decode baseA2 := witness_mul witness_baseA witness_baseA mul_baseA2
theorem witness_a : ∃ g : LyonsGroup, matrixRepresentation g = decode a := witness_mul witness_baseA2 witness_baseA2 mul_a
end Lyons.TwoRank.Matrices

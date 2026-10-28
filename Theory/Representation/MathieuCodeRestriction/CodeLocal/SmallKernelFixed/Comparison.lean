module
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.SmallKernelFixed.Geometry
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.SmallKernelFixed.Data

/-!
# Comparison of packed differences with the native Golay action

Restriction of each of the twelve native rows gives its packed complementary
word. Binary translation permutes these sixteen bits, and the checked row
differences extend to all messages by distributivity of xor. Consequently a
native Golay word is fixed exactly when its encoded packed difference is zero.
This proves the semantic comparison needed by the finite word certificates.

Source: Aschbacher--Smith, H.16.2 and H.16.8, printed pp.402--405.
-/

open Sporadic.Mathieu
open Representation.BinaryOffender
public section
namespace MathieuCode.SmallKernelFixed

private theorem xor_bits {w : Nat} (a b : BitVec w) (i : Fin w) :
    (a ^^^ b).getLsb i = (a.getLsb i ^^ b.getLsb i) := by simp

private theorem select16_bits (b : Bool) (x : BitVec 16) (i : Fin 16) :
    (select16 b x).getLsb i = (b && x.getLsb i) := by
  cases b <;> simp [select16]

private theorem select24_bits (b : Bool) (x : BitVec 24) (i : Fin 24) :
    (m24GolaySelect b x).getLsb i = (b && x.getLsb i) := by
  cases b <;> simp [m24GolaySelect]

private theorem packedRows_bits (i : Fin 12) (j : Fin 16) :
    (packedRows i).getLsb j = (m24GolayRow i).getLsb (coordinate j) := by
  revert i j
  decide +kernel

private theorem packedCode_bits (u : Fin 4096) (j : Fin 16) :
    (encode16 packedRows u).getLsb j = (m24GolayCode u).getLsb (coordinate j) := by
  simp only [encode16, m24GolayCode, xor_bits, select16_bits, select24_bits, packedRows_bits]
  rfl

private theorem eq_iff_bits (x y : BitVec 16) :
    x = y ↔ ∀ j : Fin 16, x.getLsb j = y.getLsb j := by
  constructor
  · intro h j; rw [h]
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact h ⟨i, hi⟩

private def permuteBits (n : Fin 16) (b : BitVec 16) : BitVec 16 :=
  BitVec.ofFnLE fun j => b.getLsb (xorIndex n j)

private theorem permuteBits_bits (n : Fin 16) (b : BitVec 16) (j : Fin 16) :
    (permuteBits n b).getLsb j = b.getLsb (xorIndex n j) :=
  BitVec.getLsb_ofFnLE _ _

private theorem permuteBits_xor (n : Fin 16) (a b : BitVec 16) :
    permuteBits n (a ^^^ b) = permuteBits n a ^^^ permuteBits n b := by
  apply (eq_iff_bits _ _).mpr
  intro j
  simp only [permuteBits_bits, xor_bits]

private theorem permuteBits_zero (n : Fin 16) : permuteBits n 0 = 0 := by
  apply (eq_iff_bits _ _).mpr
  intro j
  rw [permuteBits_bits]
  simp

private theorem permuteBits_select (n : Fin 16) (b : Bool) (x : BitVec 16) :
    permuteBits n (select16 b x) = select16 b (permuteBits n x) := by
  cases b
  · exact permuteBits_zero n
  · rfl

private theorem select16_xor (b : Bool) (x y : BitVec 16) :
    select16 b (x ^^^ y) = select16 b x ^^^ select16 b y := by
  cases b <;> simp [select16]

private theorem encode16_xor (r s : Fin 12 → BitVec 16) (u : Fin 4096) :
    encode16 (fun i => r i ^^^ s i) u = encode16 r u ^^^ encode16 s u := by
  simp only [encode16, select16_xor]
  ac_rfl

private theorem permuteBits_encode (n : Fin 16) (r : Fin 12 → BitVec 16) (u : Fin 4096) :
    permuteBits n (encode16 r u) = encode16 (fun i => permuteBits n (r i)) u := by
  simp only [encode16, permuteBits_xor, permuteBits_select]

private theorem differenceRows_spec (n : Fin 16) (i : Fin 12) :
    differenceRows n i = permuteBits n (packedRows i) ^^^ packedRows i := by
  revert n i
  decide +kernel

private theorem difference_eq (n : Fin 16) (u : Fin 4096) :
    encode16 (differenceRows n) u =
      permuteBits n (encode16 packedRows u) ^^^ encode16 packedRows u := by
  have h : differenceRows n = fun i => permuteBits n (packedRows i) ^^^ packedRows i :=
    funext (differenceRows_spec n)
  rw [h, encode16_xor, ← permuteBits_encode]

/-- A native Golay word is fixed exactly when its packed difference is zero. -/
theorem golayWord_fixed_iff_difference (n : Fin 16) (u : Fin 4096) :
    golayRepresentation (translation n) (golayWord u) = golayWord u ↔
      encode16 (differenceRows n) u = 0 := by
  rw [difference_eq]
  change _ ↔ (permuteBits n (encode16 packedRows u) ^^^ encode16 packedRows u = 0#16)
  rw [BitVec.xor_eq_zero_iff, eq_iff_bits, translation_fixed_iff]
  simp only [permuteBits_bits, packedCode_bits]
  apply forall_congr'
  intro j
  change (if (m24GolayCode u).getLsb (coordinate (xorIndex n j)) then (1 : ZMod 2) else 0) =
      (if (m24GolayCode u).getLsb (coordinate j) then 1 else 0) ↔ _
  cases (m24GolayCode u).getLsb (coordinate (xorIndex n j)) <;>
    cases (m24GolayCode u).getLsb (coordinate j) <;> decide


end MathieuCode.SmallKernelFixed

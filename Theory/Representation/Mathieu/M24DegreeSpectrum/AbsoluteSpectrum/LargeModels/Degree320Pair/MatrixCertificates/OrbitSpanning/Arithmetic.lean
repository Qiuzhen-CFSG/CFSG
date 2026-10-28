module

public import Mathlib.Algebra.Field.ZMod
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RowArithmetic
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.OrbitArithmetic


/-!
# Bounded orbit certificates over the binary field

The skip checker is identified with the dimension-independent J₂ orbit checker.
Its soundness recovers the recorded row words by induction on earlier prefixes;
transposition then reverses them for column actions. The inverse lemma consumes
bounded row checks for the literal stored inverse. These interfaces are used by
both degree-320 certificates below. Data provenance: `../../source/README.md`.
-/

@[expose] public section

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitCertificates
open Thompson.BinaryMatrix
open Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels

theorem rows_inverse (n : Nat) (a b : List Nat) (ha : a.length = n) (hb : b.length = n)
    (h : checkRows a b (List.ofFn (fun i : Fin n => 2^i.val)) = true) :
    decode n a.toArray * decode n b.toArray = 1 := by
  rw [product_sound_list n a b _ ha hb h]
  ext i j
  simp [decode, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

theorem eval_eq_decode (n : Nat) (a : Array Nat) : Binary.eval (ZMod 2) n a = decode n a := by
  ext i j
  exact Binary.eval_apply (ZMod 2) n a i j

theorem vector_eq (n a : Nat) : OneSixty.vector (ZMod 2) n a = fun i => bit a i.val := by
  ext i
  simp only [OneSixty.vector, bit]
  split <;> simp

theorem row_eq (a : Nat) (b : List Nat) (k : Nat) : row a b k = OneSixty.row a b k := by
  induction b generalizing k with
  | nil => rfl
  | cons x xs ih => simp only [row, OneSixty.row, ih]

def orbitStep (a b : Array Nat) (basis parents : Array Nat)
    (letters : Array Bool) (words : Array (List Bool)) (i : Nat) : Bool :=
  i == 0 || (decide (parents[i]! < i) &&
    (words[i]! == words[parents[i]!]! ++ [letters[i]!]) &&
    (skipRow basis[parents[i]!]! (if letters[i]! then b.toList else a.toList) == basis[i]!))

theorem orbit_check (n : Nat) (a b : Array Nat) (v : Nat) (basis parents : Array Nat)
    (letters : Array Bool) (words : Array (List Bool))
    (ha : a.size = n) (hb : b.size = n) (hv : basis[0]! = v) (hw : words[0]! = [])
    (hs : (List.range n).all (orbitStep a b basis parents letters words) = true) :
    OneSixty.checkOrbit n a b v basis parents letters words = true := by
  unfold orbitStep at hs
  simpa only [OneSixty.checkOrbit, skipRow_eq, shiftRow_eq_row, row_eq,
    ha, hb, hv, hw, beq_self_eq_true, Bool.true_and] using hs

theorem row_orbit (n : Nat) (a b : Array Nat) (v : Nat) (basis parents : Array Nat)
    (letters : Array Bool) (words : Array (List Bool))
    (h : OneSixty.checkOrbit n a b v basis parents letters words = true) (i : Fin n) :
    Matrix.vecMul (fun k => bit v k.val)
      (OneSixty.wordValue (decode n a) (decode n b) words[i.val]!) = decode n basis i := by
  have hh := OneSixty.orbit_sound (ZMod 2) n a b v basis parents letters words h i
  change Matrix.vecMul (fun k => bit v k.val)
    (OneSixty.wordValue (decode n a) (decode n b) words[i.val]!) = fun k => bit basis[i.val]! k.val
  simpa only [eval_eq_decode, vector_eq] using hh

theorem transpose_decode (n : Nat) (a b : Array Nat)
    (h : OneSixty.checkTranspose n a b = true) : (decode n a).transpose = decode n b := by
  simpa only [eval_eq_decode] using OneSixty.transpose_sound (ZMod 2) n a b h

theorem column_orbit (n : Nat) (a b aT bT p cols : Array Nat) (v : Nat)
    (parents : Array Nat) (letters : Array Bool) (words : Array (List Bool))
    (ha : OneSixty.checkTranspose n a aT = true) (hb : OneSixty.checkTranspose n b bT = true)
    (hp : OneSixty.checkTranspose n p cols = true)
    (h : OneSixty.checkOrbit n aT bT v cols parents letters words = true) (i : Fin n) :
    (OneSixty.wordValue (decode n a) (decode n b) words[i.val]!.reverse).mulVec
      (fun k => bit v k.val) = fun k => decode n p k i := by
  have hh := row_orbit n aT bT v cols parents letters words h i
  rw [← transpose_decode n a aT ha, ← transpose_decode n b bT hb,
    ← OneSixty.transpose_word, Matrix.vecMul_transpose] at hh
  rw [hh]
  exact congrFun (transpose_decode n p cols hp).symm i

theorem all_append (p : Nat → Bool) (a b : List Nat)
    (ha : a.all p = true) (hb : b.all p = true) : (a ++ b).all p = true := by
  simpa only [List.all_append, Bool.and_eq_true] using And.intro ha hb

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitCertificates

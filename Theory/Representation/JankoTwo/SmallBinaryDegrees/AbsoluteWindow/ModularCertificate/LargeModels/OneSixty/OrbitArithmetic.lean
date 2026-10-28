module
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.Arithmetic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Literal orbit certificates for packed binary matrices

The certificate checks each proposed orbit vector against an earlier prefix.
Strong induction recovers the complete displayed word. Transposition reverses
left-orbit words when passing from row vectors to column actions, as required
by the preserved ATLAS discovery record; no cyclicity answer is trusted.
Source conventions: `../source/README.md`.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty
open Thompson.BinaryMatrix

def vector (F : Type*) [Field F] [CharP F 2] (n : ℕ) (x : ℕ) : Fin n → F :=
  fun i => ZMod.castHom (dvd_refl 2) F (bit x i.val)

theorem vecMul_vector (F : Type*) [Field F] [CharP F 2] (n : ℕ)
    (a : ℕ) (b : Array ℕ) (hb : b.size = n) :
    Matrix.vecMul (vector F n a) (Binary.eval F n b) = vector F n (row a b.toList 0) := by
  ext j
  simp only [Matrix.vecMul, dotProduct, vector, Binary.eval, RingHom.mapMatrix_apply,
    Matrix.map_apply, decode, bit_row_array n b hb, map_sum, map_mul]

def wordValue {M : Type*} [Monoid M] (a b : M) (w : List Bool) : M :=
  (w.map fun s => if s then b else a).prod

theorem wordValue_append {M : Type*} [Monoid M] (a b : M) (u v : List Bool) :
    wordValue a b (u ++ v) = wordValue a b u * wordValue a b v := by
  simp [wordValue]

def checkOrbit (n : ℕ) (a b : Array ℕ) (v : ℕ) (basis parents : Array ℕ)
    (letters : Array Bool) (words : Array (List Bool)) : Bool :=
  (a.size == n) && (b.size == n) && (basis[0]! == v) && (words[0]! == []) &&
    (List.range n).all fun i => i == 0 ||
      (decide (parents[i]! < i) &&
       (words[i]! == words[parents[i]!]! ++ [letters[i]!]) &&
       (row basis[parents[i]!]! (if letters[i]! then b.toList else a.toList) 0 == basis[i]!))

theorem orbit_sound (F : Type*) [Field F] [CharP F 2] (n : ℕ)
    (a b : Array ℕ) (v : ℕ) (basis parents : Array ℕ)
    (letters : Array Bool) (words : Array (List Bool))
    (h : checkOrbit n a b v basis parents letters words = true) :
    ∀ i : Fin n, Matrix.vecMul (vector F n v)
      (wordValue (Binary.eval F n a) (Binary.eval F n b) words[i.val]!) =
      vector F n basis[i.val]! := by
  simp only [checkOrbit, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hv⟩, hw⟩, hs⟩ := h
  have main : ∀ i : ℕ, i < n → Matrix.vecMul (vector F n v)
      (wordValue (Binary.eval F n a) (Binary.eval F n b) words[i]!) =
      vector F n basis[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      by_cases hz : i = 0
      · subst i
        simp [hw, hv, wordValue]
      · have hh := List.all_eq_true.mp hs i (List.mem_range.mpr hi)
        simp only [Bool.or_eq_true, beq_iff_eq, hz, false_or, Bool.and_eq_true,
          decide_eq_true_eq] at hh
        obtain ⟨⟨hp, hw'⟩, hr⟩ := hh
        rw [hw', wordValue_append, ← Matrix.vecMul_vecMul, ih _ hp (lt_trans hp hi)]
        simp only [wordValue, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one]
        cases he : letters[i]! <;>
          simp only [he, Bool.false_eq_true, ↓reduceIte] at hr ⊢
        · rw [vecMul_vector F n _ a ha, hr]
        · rw [vecMul_vector F n _ b hb, hr]
  intro i
  exact main i.val i.isLt

def checkTranspose (n : ℕ) (a b : Array ℕ) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j =>
    a[j]!.testBit i == b[i]!.testBit j

theorem transpose_sound (F : Type*) [Field F] [CharP F 2] (n : ℕ)
    (a b : Array ℕ) (h : checkTranspose n a b = true) :
    (Binary.eval F n a).transpose = Binary.eval F n b := by
  ext i j
  have hh := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  have hh' : a[j.val]!.testBit i.val = b[i.val]!.testBit j.val :=
    of_decide_eq_true (List.all_eq_true.mp hh j.val (List.mem_range.mpr j.isLt))
  simp only [Matrix.transpose_apply, Binary.eval_apply, hh']

theorem transpose_word {F : Type*} [Field F] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) F) (w : List Bool) :
    (wordValue A B w.reverse).transpose = wordValue A.transpose B.transpose w := by
  induction w with
  | nil => simp [wordValue]
  | cons s w ih =>
    rw [List.reverse_cons, wordValue_append, Matrix.transpose_mul, ih]
    cases s <;> simp [wordValue]

theorem wordValue_mem {F : Type*} [Field F] {n : ℕ}
    (S : Subalgebra F (Matrix (Fin n) (Fin n) F))
    (A B : Matrix (Fin n) (Fin n) F) (hA : A ∈ S) (hB : B ∈ S) (w : List Bool) :
    wordValue A B w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons s w ih =>
    change (if s then B else A) * wordValue A B w ∈ S
    apply S.mul_mem _ ih
    cases s
    · exact hA
    · exact hB

def checkOuter (n : ℕ) (v l : ℕ) (c : Array ℕ) : Bool :=
  (List.range n).all fun i => c[i]! == if v.testBit i then l else 0

theorem outer_sound (F : Type*) [Field F] [CharP F 2] (n : ℕ)
    (v l : ℕ) (c : Array ℕ) (h : checkOuter n v l c = true) :
    Binary.eval F n c = Matrix.vecMulVec (vector F n v) (vector F n l) := by
  ext i j
  have hi : c[i.val]! = if v.testBit i.val then l else 0 :=
    of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  simp only [Binary.eval_apply, hi, Matrix.vecMulVec_apply, vector, bit]
  cases hv : v.testBit i.val <;> cases hl : l.testBit j.val <;> simp [hl]
end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty

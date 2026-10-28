module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.Projector
public import Mathlib.Data.List.OfFn

/-!
# Exact binary dot products in degree 1792

A divide-and-conquer parity fold discards processed bits at each step. Division
by a power of two implements the shift without a long recursive shift reduction.
The sequential checker reads the literal matrix rows once and consumes the
output vector one bit at a time. Its soundness theorem gives the original
matrix's left action on columns, without transposing the ATLAS convention.

The parity argument adapts the project's Janko4 `FiniteAlgebra.Fast` arithmetic;
it is independent of that group. The actual consumer is `KernelReduction`. Source matrices and attribution: `../../source/README.md` and
`../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate
open Thompson.BinaryMatrix Matrix

def vector (x : Nat) : Fin 1792 → ZMod 2 := fun i => bit x i.val

theorem vector_xor (x y : Nat) : vector (x ^^^ y) = vector x + vector y := by
  ext i
  exact bit_xor x y i.val

theorem vector_zero : vector 0 = 0 := by
  ext i
  simp [vector, bit]

def foldPow : Nat → Nat → Nat
  | 0, x => x
  | k+1, x => foldPow k ((x % 2^(2^k)) ^^^ (x / 2^(2^k)))

theorem sum_bits_split (n m x : Nat) :
    (∑ i : Fin (n+m), bit x i.val) =
      (∑ i : Fin n, bit x i.val) + (∑ i : Fin m, bit (x >>> n) i.val) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd, bit, Nat.testBit_shiftRight]

theorem bit_foldPow (k x : Nat) :
    bit (foldPow k x) 0 = ∑ i : Fin (2^k), bit x i.val := by
  induction k generalizing x with
  | zero =>
    change bit x 0 = ∑ i : Fin 1, bit x i.val
    rw [Fin.sum_univ_one]
    rfl
  | succ k ih =>
    rw [foldPow, ih, show 2^(k+1) = 2^k+2^k by omega, sum_bits_split]
    simp only [bit_xor, Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      simp only [bit, Nat.testBit_mod_two_pow, i.isLt, decide_true, Bool.true_and]
    · rw [← Nat.shiftRight_eq_div_pow]

def parity1792 (x : Nat) : Nat := foldPow 11 (x % 2^1792)

theorem bit_parity1792 (x : Nat) :
    bit (parity1792 x) 0 = ∑ i : Fin 1792, bit x i.val := by
  rw [parity1792, bit_foldPow, show 2^11 = 1792+256 from rfl, sum_bits_split]
  have hz : (∑ i : Fin 256, bit ((x % 2^1792) >>> 1792) i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [bit, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow,
      show ¬1792+i.val < 1792 by omega, decide_false, Bool.false_and,
      Bool.false_eq_true, if_false]
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  simp only [bit, Nat.testBit_mod_two_pow, i.isLt, decide_true, Bool.true_and]

theorem dot_spec (x y : Nat) :
    bit (parity1792 (x &&& y)) 0 = dotProduct (vector x) (vector y) := by
  rw [bit_parity1792]
  apply Finset.sum_congr rfl
  intro i _
  simp only [vector, bit, Nat.testBit_and]
  cases x.testBit i.val <;> cases y.testBit i.val <;> decide

def checkAction (u v : Nat) : List Nat → Bool
  | [] => true
  | r :: rs => ((parity1792 (r &&& u)).testBit 0 == v.testBit 0) &&
    checkAction u (v / 2) rs

theorem checkAction_get (u v : Nat) (rs : List Nat) (h : checkAction u v rs = true)
    (i : Nat) (hi : i < rs.length) :
    bit (parity1792 (rs[i]! &&& u)) 0 = bit v i := by
  induction rs generalizing v i with
  | nil => simp at hi
  | cons r rs ih =>
    simp only [checkAction, Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero => simp only [List.getElem!_cons_zero, bit, h.1]
    | succ i =>
      simpa only [List.getElem!_cons_succ, bit, Nat.testBit_div_two] using
        ih (v / 2) h.2 i (by simpa using hi)

theorem action_sound (rs : Array Nat) (hs : rs.size = 1792) (u v : Nat)
    (h : checkAction u v rs.toList = true) :
    (decode 1792 rs).mulVec (vector u) = vector v := by
  ext i
  have hi := checkAction_get u v rs.toList h i.val (by simp [hs])
  rw [dot_spec] at hi
  simpa [mulVec, dotProduct, vector, decode, Array.getElem!_eq_getD,
    Array.getD_eq_getD_getElem?] using hi
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate

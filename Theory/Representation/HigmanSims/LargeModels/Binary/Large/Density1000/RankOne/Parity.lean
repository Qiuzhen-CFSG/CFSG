module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Arithmetic
/-!
# Packed dot products for the degree-1000 column kernel

Ten XOR folds compute the parity of the low 1000 bits, padding by 24 zero
bits to a power of two. `dot_spec` proves that applying this operation to a
bitwise intersection is the ordinary dot product over `ZMod 2`. This avoids
transposing the source matrix in the left-kernel-vector calculation.

Adapted from this repository's M24 degree-1792 `RankOne/Arithmetic.lean`,
which follows the Janko4 parity argument. Original code is Apache-2.0.
The actual HS source and its attribution are in `Binary/source/README.md`.
-/

@[expose] public section
open Thompson.BinaryMatrix Matrix
open scoped BigOperators
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
open RowArithmetic

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

def parity1000 (x : Nat) : Nat := foldPow 10 (x % 2^1000)

theorem bit_parity1000 (x : Nat) :
    bit (parity1000 x) 0 = ∑ i : Fin 1000, bit x i.val := by
  rw [parity1000, bit_foldPow, show 2^10 = 1000+24 from rfl, sum_bits_split]
  have hz : (∑ i : Fin 24, bit ((x % 2^1000) >>> 1000) i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [bit, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow,
      show ¬1000+i.val < 1000 by omega, decide_false, Bool.false_and,
      Bool.false_eq_true, if_false]
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  simp only [bit, Nat.testBit_mod_two_pow, i.isLt, decide_true, Bool.true_and]

theorem dot_spec (x y : Nat) :
    bit (parity1000 (x &&& y)) 0 = dotProduct (vector 1000 x) (vector 1000 y) := by
  rw [bit_parity1000]
  apply Finset.sum_congr rfl
  intro i _
  simp only [vector, bit, Nat.testBit_and]
  cases x.testBit i.val <;> cases y.testBit i.val <;> decide

def RowTree.checkZero (u : ℕ) : RowTree → Bool
  | .leaf rs => rs.all fun r => decide (parity1000 (r &&& u) = 0)
  | .node _ l r => l.checkZero u && r.checkZero u

theorem RowTree.checkZero_mem (t : RowTree) (u : ℕ) (h : t.checkZero u = true)
    (r : ℕ) (hr : r ∈ t.rows) : parity1000 (r &&& u) = 0 := by
  induction t with
  | leaf rs =>
    exact of_decide_eq_true (List.all_eq_true.mp h r hr)
  | node n l r ihl ihr =>
    simp only [RowTree.checkZero, Bool.and_eq_true] at h
    rcases List.mem_append.mp hr with hr | hr
    · exact ihl h.1 hr
    · exact ihr h.2 hr

theorem RowTree.mulVec_zero (t : RowTree) (rs : Array ℕ)
    (halign : t.rows = rs.toList) (hs : rs.size = 1000) (u : ℕ)
    (h : t.checkZero u = true) :
    (decode 1000 rs).mulVec (vector 1000 u) = 0 := by
  funext i
  have hi : i.val < rs.toList.length := by
    rw [Array.length_toList, hs]
    exact i.isLt
  have hm : rs.toList[i.val]! ∈ t.rows := by
    rw [halign, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  have hz := t.checkZero_mem u h _ hm
  have he := dot_spec rs.toList[i.val]! u
  rw [hz] at he
  have hb : bit 0 0 = 0 := by decide
  rw [hb] at he
  simpa only [mulVec, dotProduct, decode, vector, Array.getElem!_toList, Pi.zero_apply]
    using he.symm

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

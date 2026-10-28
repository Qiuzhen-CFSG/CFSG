module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.ModelComparison.Data
/-!
# Binary arithmetic used by the Rudvalis orbit certificate

Decoding a packed word turns XOR into vector addition. Consequently the
checked column combination is the actual matrix action on `Space`. Bounded
words are determined by their coordinates. A balanced Boolean enumeration
keeps the finite orbit certificate shallow.

Source: elementary GF(2) linear algebra, with the ATLAS bit convention
specified in `Data`.
-/

@[expose] public section
open scoped BigOperators
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.ModelComparison
abbrev bit (x i : Nat) : ZMod 2 := if x.testBit i then 1 else 0
def bits (x : Nat) : Space := fun i => bit x i.val
lemma bits_xor (x y : Nat) : bits (x ^^^ y) = bits x + bits y := by
  funext i
  simp only [bits, bit, Nat.testBit_xor, Pi.add_apply]
  cases x.testBit i.val <;> cases y.testBit i.val <;> decide
lemma bits_zero : bits 0 = 0 := by ext i; simp [bits, bit]
lemma bits_rowRange (x : Nat) (r : Nat → Nat) (start n : Nat) :
    bits (PackedBinaryRows.rowRange x r start n) =
      ∑ k ∈ Finset.range n, bit x (start+k) • bits (r (start+k)) := by
  induction n with
  | zero => simp [PackedBinaryRows.rowRange, bits_zero]
  | succ n ih =>
    rw [PackedBinaryRows.rowRange, bits_xor, ih, Finset.sum_range_succ]
    congr 1
    cases h : x.testBit (start+n) <;> simp [h, bit, bits_zero]
lemma bits_packedAction (cs : Array Nat) (hlen : cs.size = 28) (x : Nat) :
    bits (packedAction cs x) = ∑ j : Fin 28, bits x j • bits cs[j.val]! := by
  rw [packedAction, ← PackedBinaryRows.rowRange_eq_blockProduct x
    (fun i => cs[i]!) 0 28 cs hlen (by intro i; simp)]
  rw [bits_rowRange]
  exact (Fin.sum_univ_eq_sum_range (fun j => bit x j • bits cs[j]!) 28).symm
lemma packedAction_matrix (cs : Array Nat) (M : Matrix (Fin 28) (Fin 28) (ZMod 2))
    (hlen : cs.size = 28) (hm : ∀ i j, M i j = bit cs[j.val]! i.val) (x : Nat) :
    bits (packedAction cs x) = Matrix.toLin' M (bits x) := by
  rw [bits_packedAction cs hlen]
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, bits]
  apply Finset.sum_congr rfl
  intro j _
  rw [hm, mul_comm]
lemma bits_injective_bounded {x y : Nat} (hx : x < 2^28) (hy : y < 2^28)
    (h : bits x = bits y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 28
  · have hh := congrFun h ⟨i, hi⟩
    change (if x.testBit i then (1 : ZMod 2) else 0) =
      (if y.testBit i then (1 : ZMod 2) else 0) at hh
    cases ha : x.testBit i <;> cases hb : y.testBit i <;> simp_all
  · have hp : 2^28 ≤ 2^i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy hp)]
lemma bits_two_pow (i : Fin 28) : bits (2^i.val) = Pi.single i 1 := by
  ext j
  simp [bits, bit, Nat.testBit_two_pow, Pi.single_apply, Fin.ext_iff, eq_comm]

def checkTree (f : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => f start
  | n+1 => checkTree f start n && checkTree f (start + 2^n) n

lemma checkTree_spec (f : Nat → Bool) (depth start : Nat)
    (h : checkTree f start depth = true) : ∀ i, i < 2^depth → f (start+i) = true := by
  induction depth generalizing start with
  | zero =>
    intro i hi
    have : i = 0 := by simpa using hi
    simpa [this, checkTree] using h
  | succ n ih =>
    rw [checkTree, Bool.and_eq_true] at h
    intro i hi
    by_cases hil : i < 2^n
    · exact ih start h.1 i hil
    · have hip : i - 2^n < 2^n := by
        rw [Nat.pow_succ] at hi
        omega
      have hr := ih (start+2^n) h.2 (i-2^n) hip
      have he : start+2^n+(i-2^n) = start+i := by omega
      simpa only [he] using hr

lemma allOrbit (P : Fin 4060 → Prop) [DecidablePred P]
    (h : checkTree (fun n => decide (P ⟨n % 4060, Nat.mod_lt _ (by decide)⟩))
      0 12 = true) : ∀ i, P i := by
  intro i
  have hi : i.val < 2^12 := lt_of_lt_of_le i.isLt (by decide)
  have hh := of_decide_eq_true (checkTree_spec _ 12 0 h i.val hi)
  simpa only [Nat.zero_add, Nat.mod_eq_of_lt i.isLt] using hh

end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.ModelComparison

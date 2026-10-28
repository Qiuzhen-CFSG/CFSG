module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Ambient
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.RowArithmetic
/-!
# Packing the exact exterior-square minor coordinates

The triangular packing operation concatenates the lower and upper source-bit
patterns. Its bit theorem follows by induction over triangular intervals;
`pair_index` then identifies the published exterior basis. This avoids any
finite computation of the inverse dependent equivalence used by `pair`.

The numerical tables and minor identities consume these theorems in
`AmbientRows`. Source and conventions: ATLAS HSG1-f2r56B0/HSG1-f2r1000B0,
`Binary/source/README.md` and `Exterior1000/source/README.md`.
Original repository code under Apache 2.0; source attribution is retained.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining
open Thompson.BinaryMatrix

def triangular (n : ℕ) : ℕ := n * (n - 1) / 2

theorem triangular_succ (n : ℕ) : triangular (n + 1) = triangular n + n :=
by
  simp only [triangular, ← Finset.sum_range_id]
  exact Finset.sum_range_succ _ n

theorem triangular_mono : Monotone triangular := by
  apply monotone_nat_of_le_succ
  intro n
  rw [triangular_succ]
  omega

theorem triangular_eq (n : ℕ) : triangular n = n * (n - 1) / 2 :=
  rfl

def joinBits (n lo hi : ℕ) : ℕ := 2^n * hi + lo % 2^n

theorem joinBits_low (n lo hi i : ℕ) (h : i < n) :
    (joinBits n lo hi).testBit i = lo.testBit i := by
  rw [joinBits, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  simp only [h, if_true, Nat.testBit_mod_two_pow, decide_true, Bool.true_and]

theorem joinBits_high (n lo hi i : ℕ) :
    (joinBits n lo hi).testBit (n + i) = hi.testBit i := by
  rw [joinBits, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  simp

def trianglePack (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => joinBits (triangular n) (trianglePack f n) (f n)

theorem trianglePack_bit (f : ℕ → ℕ) (n j k : ℕ) (hj : j < n) (hk : k < j) :
    (trianglePack f n).testBit (triangular j + k) = (f j).testBit k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [trianglePack]
    by_cases h : j < n
    · rw [joinBits_low, ih h]
      have hmono := triangular_mono (show j + 1 ≤ n by omega)
      rw [triangular_succ] at hmono
      omega
    · have : j = n := by omega
      subst j
      exact joinBits_high _ _ _ _

def highBits (x : ℕ) : ℕ := trianglePack (fun j => if x.testBit j then 2^j - 1 else 0) 56

def lowBits (x : ℕ) : ℕ := trianglePack (fun j => x % 2^j) 56

theorem highBits_bit (x : ℕ) (i : Fin 1540) :
    (highBits x).testBit i.val = x.testBit (pair i).1.val := by
  have idx : triangular (pair i).1.val + (pair i).2.val = i.val := by
    rw [triangular_eq, pair_index]
  rw [highBits, ← idx, trianglePack_bit _ _ _ _ (pair i).1.isLt (pair_lt i)]
  cases x.testBit (pair i).1.val <;> simp [Nat.testBit_two_pow_sub_one, pair_lt]

theorem lowBits_bit (x : ℕ) (i : Fin 1540) :
    (lowBits x).testBit i.val = x.testBit (pair i).2.val := by
  have idx : triangular (pair i).1.val + (pair i).2.val = i.val := by
    rw [triangular_eq, pair_index]
  rw [lowBits, ← idx, trianglePack_bit _ _ _ _ (pair i).1.isLt (pair_lt i)]
  simp only [Nat.testBit_mod_two_pow, show (pair i).2.val < (pair i).1.val from pair_lt i,
    decide_true, Bool.true_and]

end Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining

module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.Assembly
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Packed row actions for the larger Baby Monster primes

Bit `j` of a natural number represents coordinate `j` of a binary row vector.
The action XORs the source rows selected by those bits. Its correctness is
proved by converting each XOR bit to addition in `ZMod 2`, and then identifying
the resulting finite sum with `Matrix.vecMul`.

The matrices and bit convention are the unchanged ATLAS data documented in
`LowerBound/source/README.md`. This module proves arithmetic soundness only;
concrete orbit evaluations remain separate certificates.
-/

@[expose] public section

open scoped BigOperators
namespace BabyMonster.OrderLowerBound.RemainingFactors.LargePrimes
abbrev bit (x j : ℕ) : ZMod 2 := if x.testBit j then 1 else 0
lemma bit_xor (x y j : ℕ) : bit (x ^^^ y) j = bit x j + bit y j := by
  simp only [bit, Nat.testBit_xor]
  cases x.testBit j <;> cases y.testBit j <;> decide

def rowProduct (x : ℕ) (rows : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => rowProduct x rows n ^^^ (if x.testBit n then rows n else 0)

lemma bit_rowProduct (x : ℕ) (rows : ℕ → ℕ) (n j : ℕ) :
    bit (rowProduct x rows n) j = ∑ k ∈ Finset.range n, bit x k * bit (rows k) j := by
  induction n with
  | zero => simp [rowProduct, bit]
  | succ n ih =>
    rw [rowProduct, bit_xor, ih, Finset.sum_range_succ]
    congr 1
    cases h : x.testBit n <;> simp [bit, h]

def vector (x : ℕ) : Fin 4370 → ZMod 2 := fun i => bit x i.val

def rows (b : Bool) (i : ℕ) : ℕ :=
  if h : i < 4370 then if b then atlasBRow ⟨i,h⟩ else atlasARow ⟨i,h⟩ else 0

def action (b : Bool) (x : ℕ) : ℕ := rowProduct x (rows b) 4370

theorem action_correct (b : Bool) (x : ℕ) :
    vector (action b x) = Matrix.vecMul (vector x) (if b then atlasB else atlasA) := by
  funext j
  change bit (rowProduct x (rows b) 4370) j.val = _
  rw [bit_rowProduct]
  change _ = ∑ i : Fin 4370, bit x i.val * (if b then atlasB else atlasA) i j
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := i.isLt
  cases b <;> simp [rows, hi', atlasA, atlasB, bit]
end BabyMonster.OrderLowerBound.RemainingFactors.LargePrimes

module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.RowArithmetic
open Representation.HigmanSims.LargeModels.Binary.Large.RowArithmetic
open Thompson.BinaryMatrix
/-!
# Block arithmetic and packed Kronecker rows for the HS tensor certificate

The block evaluator is proved equal to the sequential checker in `RowArithmetic`.
The tensor-row bit formula identifies each packed column with the product of the
literal factor entries, with the second coordinate fastest. These structural
lemmas avoid repeating either matrix sums or bit interpretation in numeric checks.

Source: ATLAS HSG1-f2r20B0, HSG1-f2r56B0 and HSG1-f2r518B0;
see `Binary/source/README.md`. Original Lean code is Apache-2.0.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorB

def blocksCombine : List (List ℕ) → ℕ → ℕ
  | [], _ => 0
  | b :: bs, x => combine b x ^^^ blocksCombine bs (x >>> b.length)

theorem blocksCombine_eq (bs : List (List ℕ)) (x : ℕ) :
    blocksCombine bs x = combine bs.flatten x := by
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih => simp only [blocksCombine, List.flatten_cons, combine_append, ih]

def tensorRow (n w x y : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 => (if x.testBit 0 then y else 0) ||| (tensorRow n w (x >>> 1) y <<< w)

theorem tensorRow_bit (n w x y a b : ℕ) (ha : a < n) (hb : b < w)
    (hy : y < 2 ^ w) :
    (tensorRow n w x y).testBit (w * a + b) = (x.testBit a && y.testBit b) := by
  induction n generalizing x a with
  | zero => omega
  | succ n ih =>
    cases a with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, tensorRow, Nat.testBit_or, Nat.testBit_shiftLeft]
      simp only [show ¬b ≥ w by omega, decide_false, Bool.false_and, Bool.or_false]
      cases x.testBit 0 <;> simp
    | succ a =>
      have hw : w ≤ w * (a + 1) + b := by simp only [Nat.mul_add, Nat.mul_one]; omega
      have hy' : y < 2 ^ (w * (a + 1) + b) :=
        lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hw)
      have hz : (if x.testBit 0 then y else 0).testBit (w * (a + 1) + b) = false := by
        cases x.testBit 0 <;> simp [Nat.testBit_lt_two_pow hy']
      rw [tensorRow, Nat.testBit_or, hz, Bool.false_or, Nat.testBit_shiftLeft]
      simp only [hw, decide_true, Bool.true_and]
      rw [show w * (a + 1) + b - w = w * a + b by simp only [Nat.mul_add, Nat.mul_one]; omega,
        ih (x >>> 1) a (by omega), Nat.testBit_shiftRight]
      rw [Nat.add_comm 1 a]
theorem range_append {P : ℕ → Prop} (start left right : ℕ)
    (hl : ∀ i : Fin left, P (start + i.val))
    (hr : ∀ i : Fin right, P (start + left + i.val)) :
    ∀ i : Fin (left + right), P (start + i.val) := by
  intro i
  by_cases h : i.val < left
  · exact hl ⟨i.val, h⟩
  · have hi : i.val - left < right := by omega
    have he : start + left + (i.val - left) = start + i.val := by omega
    exact he ▸ hr ⟨i.val - left, hi⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorB

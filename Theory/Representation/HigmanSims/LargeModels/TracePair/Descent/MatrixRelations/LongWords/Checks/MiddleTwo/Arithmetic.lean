module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Products

/-!
# Products of packed rows with evaluated accumulator states

This computes the same ordered GF(4) row product as `Packed.rowProduct`.
Dividing each coefficient plane by two advances one input coordinate. Forcing
both accumulator planes after each operation prevents repeated kernel work.
The proof below relates this recurrence to the existing packed arithmetic;
all numerical certificates are checked separately by the kernel.

The application is to the literal HSG1-f4r896aB0 matrices. Their provenance and
encoding are recorded in `TracePair/source/README.md`; the exact circuit is in
`LongWords/source/circuit.json`. No matrix or circuit definition is changed.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo
open Certificates Packed

/-- Evaluate a natural-number state before passing it to the next operation. -/
def forceNat {α : Sort*} (n : ℕ) (f : ℕ → α) : α :=
  match n with
  | 0 => f 0
  | n + 1 => f (n + 1)
private theorem forceNat_eq {α : Sort*} (n : ℕ) (f : ℕ → α) : forceNat n f = f n := by
  cases n <;> rfl

def product : Nat → Nat → Mat → Nat → Nat → Row
  | _, _, [], p, q => (p, q)
  | x, y, (u,v)::bs, p, q =>
      forceNat (x / 2) fun xx => forceNat (y / 2) fun yy =>
      forceNat (if x % 2 = 1 then p ^^^ u else p) fun pp =>
      forceNat (if x % 2 = 1 then q ^^^ v else q) fun qq =>
      forceNat (if y % 2 = 1 then pp ^^^ v else pp) fun ppp =>
      forceNat (if y % 2 = 1 then qq ^^^ (u ^^^ v) else qq) fun qqq =>
      product xx yy bs ppp qqq

private theorem rowProductFrom_shift (x y : Nat) (bs : Mat) (k : Nat) :
    rowProductFrom (x / 2, y / 2) bs k = rowProductFrom (x,y) bs (k+1) := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih => simp only [rowProductFrom, Nat.testBit_div_two, ih]

private theorem product_eq (x y : Nat) (bs : Mat) (p q : Nat) :
    product x y bs p q = Base.addRow (p,q) (rowProduct (x,y) bs) := by
  induction bs generalizing x y p q with
  | nil => simp [product, rowProduct, rowProductFrom, Base.addRow]
  | cons b bs ih =>
    rcases b with ⟨u,v⟩
    simp only [product, forceNat_eq, ih]
    simp only [rowProduct, rowProductFrom_shift, rowProductFrom]
    simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]
    by_cases hx : x % 2 = 1 <;> by_cases hy : y % 2 = 1 <;>
      simp only [hx, hy, decide_true, decide_false, Bool.false_eq_true,
        if_true, if_false, Base.addRow, Base.timesT, Nat.zero_xor, Nat.xor_zero]
    all_goals apply Prod.ext <;> dsimp <;> ac_rfl

theorem rowProduct_eq (a : Row) (bs : Mat) :
    product a.1 a.2 bs 0 0 = rowProduct a bs := by
  rw [product_eq]
  simp [Base.addRow]


end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo

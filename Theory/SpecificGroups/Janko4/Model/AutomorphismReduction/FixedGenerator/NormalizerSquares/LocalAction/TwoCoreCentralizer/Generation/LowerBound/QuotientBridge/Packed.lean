module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientModel

/-!
# Rectangular binary row certificates

Right row multiplication is checked by XOR of the selected rows, then
transported to ordinary rectangular matrix multiplication. This extends the
square packed arithmetic used for the original ATLAS J4 matrices.
The subquotient certificates use dimensions 112, 62 and 12.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.QuotientBridge
open Janko4.GeneratorCertificates

def decode {m : ℕ} (n : ℕ) (rows : Vector ℕ m) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bit (rows.get i) j.val

def rowProduct {n : ℕ} (x : ℕ) (ys : Vector ℕ n) : ℕ :=
  xorList (List.ofFn (fun k : Fin n => if x.testBit k.val then ys.get k else 0))

theorem decode_product {m n k : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n) :
    decode k (Vector.ofFn (fun i => rowProduct (xs.get i) ys)) =
      decode n xs * decode k ys := by
  funext i j
  simp only [decode, get_ofFn]
  rw [rowProduct, bit_xorList, List.map_ofFn, List.sum_ofFn, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [decode, bit]
  cases h : (xs.get i).testBit a.val <;> simp [h]

theorem product_eq_of_rows {m n k : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n)
    (zs : Vector ℕ m) (h : ∀ i, rowProduct (xs.get i) ys = zs.get i) :
    decode n xs * decode k ys = decode k zs := by
  rw [← decode_product]
  congr 1
  apply Vector.ext
  intro i hi
  change (Vector.ofFn _).get ⟨i, hi⟩ = zs.get ⟨i, hi⟩
  rw [get_ofFn, h]

theorem products_eq_of_rows {m n k l : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n)
    (zs : Vector ℕ m) (ws : Vector ℕ l)
    (h : ∀ i, rowProduct (xs.get i) ys = rowProduct (zs.get i) ws) :
    decode n xs * decode k ys = decode l zs * decode k ws := by
  rw [← decode_product, ← decode_product]
  congr 1
  apply Vector.ext
  intro i hi
  change (Vector.ofFn _).get ⟨i, hi⟩ = (Vector.ofFn _).get ⟨i, hi⟩
  simpa only [get_ofFn] using h ⟨i, hi⟩

theorem decode_one (n : ℕ) :
    decode n (Vector.ofFn (fun i : Fin n => 2 ^ i.val)) = 1 := by
  funext i j
  simp only [decode, get_ofFn, bit, Nat.testBit_two_pow, decide_eq_true_eq,
    Matrix.one_apply, Fin.ext_iff]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.QuotientBridge

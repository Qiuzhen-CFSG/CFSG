module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Foundation

/-!
# Packed arithmetic for restriction pullback coefficients

Rows encode binary matrices with the low bit in column zero. XOR selection
computes rectangular matrix multiplication, and packing the columns computes
transpose. The resulting pullback evaluator is proved equal to `upperValue`
on the ordinary product of the decoded matrices. No assertion about a table
of coefficients is assumed in these arithmetic lemmas.

The dot-product recurrence also certifies the constant terms without unfolding
matrix sums. Source conventions and ATLAS attribution: the polynomial
certificate's `source/README.md` and `Janko4/Model/Data.lean`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate
open GeneratorCertificates
open scoped Matrix
namespace PullbackCoefficients

def dotBits : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n+1, x, y => if x = 0 then 0 else
      (if x.testBit 0 && y.testBit 0 then 1 else 0) ^^^ dotBits n (x >>> 1) (y >>> 1)

theorem bit_dotBits (n x y : ℕ) :
    bit (dotBits n x y) 0 = ∑ j : Fin n, bit x j.val * bit y j.val := by
  induction n generalizing x y with
  | zero => simp [dotBits, bit]
  | succ n ih =>
    by_cases hx : x = 0
    · subst x
      simp [dotBits, bit]
    · rw [dotBits, if_neg hx, bit_xor, ih, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, bit, Nat.testBit_shiftRight]
      congr 1
      · have hd : ∀ a b : Bool,
            bit (if a && b then 1 else 0) 0 =
              (if a then (1 : ZMod 2) else 0) * (if b then 1 else 0) := by decide
        exact hd (x.testBit 0) (y.testBit 0)
      · apply Finset.sum_congr rfl
        intro j _
        simp only [Nat.add_comm 1]

def weightRow (w : ℕ) (i : Fin 50) : ℕ :=
  (w >>> (i.val * 50 - i.val * (i.val+1)/2)) <<< (i.val+1)

theorem bit_weightRow (w : ℕ) (i j : Fin 50) :
    bit (weightRow w i) j.val = if i < j then bit w (upperSlot i j) else 0 := by
  simp only [weightRow, bit, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hij : i < j
  · have hle : i.val+1 ≤ j.val := hij
    simp only [hle, decide_true, Bool.true_and, hij, if_true, upperSlot]
    congr 2
  · have hle : ¬i.val+1 ≤ j.val := by omega
    simp [hij, hle]

def upperBits (w : ℕ) (rows : Vector ℕ 50) : ℕ :=
  xorList (List.ofFn (fun i : Fin 50 => dotBits 50 (weightRow w i) (rows.get i)))

theorem upperBits_spec (w : ℕ) (rows : Vector ℕ 50) :
    bit (upperBits w rows) 0 = upperValue w (decodeRestrictionRows rows) := by
  unfold upperBits
  rw [bit_xorList, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, bit_dotBits, bit_weightRow, upperValue, decodeRestrictionRows]


/-- Decode rows into a rectangular binary matrix. -/
def rowsMatrix {m n : ℕ} (rows : Vector ℕ m) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bit (rows.get i) j.val

/-- XOR the rows selected by a binary row. -/
def rowProduct {n : ℕ} (x : ℕ) (rows : Vector ℕ n) : ℕ :=
  xorList (List.ofFn (fun k : Fin n => if x.testBit k.val then rows.get k else 0))

def rowsProduct {m n : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n) : Vector ℕ m :=
  Vector.ofFn (fun i => rowProduct (xs.get i) ys)

theorem rowsMatrix_product {l m n : ℕ} (xs : Vector ℕ l) (ys : Vector ℕ m) :
    rowsMatrix (n := n) (rowsProduct xs ys) =
      rowsMatrix (n := m) xs * rowsMatrix (n := n) ys := by
  funext i j
  simp only [rowsMatrix, rowsProduct, get_ofFn]
  rw [rowProduct, bit_xorList, List.map_ofFn, List.sum_ofFn, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  cases h : (xs.get i).testBit k.val <;> simp [rowsMatrix, bit, h]

/-- Pack the columns of a rectangular row array. -/
def rowsTranspose {m : ℕ} (n : ℕ) (xs : Vector ℕ m) : Vector ℕ n :=
  Vector.ofFn (fun j => xorList (List.ofFn (fun i : Fin m =>
    if (xs.get i).testBit j.val then 2^i.val else 0)))

theorem rowsMatrix_transpose {m n : ℕ} (xs : Vector ℕ m) :
    rowsMatrix (n := m) (rowsTranspose n xs) = (rowsMatrix (n := n) xs)ᵀ := by
  funext i j
  simp only [rowsMatrix, rowsTranspose, get_ofFn, bit_xorList, List.map_ofFn,
    List.sum_ofFn, Matrix.transpose_apply]
  calc
    (∑ k : Fin m, bit (if (xs.get k).testBit i.val then 2 ^ k.val else 0) j.val) =
        ∑ k : Fin m, if k = j then bit (xs.get j) i.val else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = j
      · subst k
        cases h : (xs.get j).testBit i.val <;> simp [h, bit]
      · have hv : k.val ≠ j.val := fun h => hk (Fin.ext h)
        cases h : (xs.get k).testBit i.val <;> simp [bit, hk, hv]
    _ = _ := by simp

/-- Compute the upper triangular functional of a packed matrix pullback. -/
def pullbackBits (w : ℕ) (R A B : Vector ℕ 50) : ℕ :=
  upperBits w (rowsProduct (rowsProduct (rowsTranspose 50 A) R) B)

theorem pullbackBits_spec (w : ℕ) (R A B : Vector ℕ 50) :
    bit (pullbackBits w R A B) 0 =
      upperValue w ((decodeRestrictionRows A)ᵀ * decodeRestrictionRows R *
        decodeRestrictionRows B) := by
  rw [pullbackBits, upperBits_spec]
  change upperValue w (rowsMatrix (rowsProduct (rowsProduct (rowsTranspose 50 A) R) B)) = _
  rw [rowsMatrix_product, rowsMatrix_product, rowsMatrix_transpose]
  rfl

end PullbackCoefficients
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate

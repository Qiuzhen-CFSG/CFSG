module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Structure

/-!
# A checked Boolean evaluator for the fifth compound matrix

Laplace expansion computes determinants over the binary field using XOR and
conjunction. The soundness theorem identifies the evaluator with `Matrix.det`;
finite checks of the saved rows can therefore avoid the abstract permutation sum.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates
open scoped BigOperators

def binaryValue (b : Bool) : ZMod 2 := if b then 1 else 0

lemma binaryValue_xor : ∀ a b,
    binaryValue (Bool.xor a b) = binaryValue a + binaryValue b := by decide +kernel

lemma binaryValue_and : ∀ a b,
    binaryValue (a && b) = binaryValue a * binaryValue b := by decide +kernel

lemma binaryValue_fold (l : List Bool) :
    binaryValue (l.foldr Bool.xor false) = (l.map binaryValue).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, binaryValue_xor, ih]

/-- Laplace expansion with characteristic-two signs and short-circuit zero terms. -/
def binaryDet : (n : ℕ) → (Fin n → Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, m => (List.ofFn (fun j : Fin (n + 1) =>
      m 0 j && binaryDet n (fun k l => m k.succ (j.succAbove l)))).foldr Bool.xor false

lemma binaryValue_binaryDet (n : ℕ) (m : Fin n → Fin n → Bool) :
    binaryValue (binaryDet n m) = (Matrix.of (fun i j => binaryValue (m i j))).det := by
  induction n with
  | zero => simp [binaryDet, binaryValue]
  | succ n ih =>
    rw [binaryDet, binaryValue_fold, List.map_ofFn, List.sum_ofFn,
      Matrix.det_succ_row_zero]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Function.comp_apply]
    rw [binaryValue_and, ih]
    have hn : (-1 : ZMod 2) = 1 := by decide +kernel
    simp only [hn, one_pow, one_mul, Matrix.of_apply]
    rfl

/-- Boolean entries of the literal two eleven-dimensional column matrices. -/
def codeBit (b : Bool) (i j : Fin 11) : Bool :=
  ((if b then codeRowsB else codeRowsA)[i.val]!).testBit j.val

lemma binaryValue_codeBit (b : Bool) (i j : Fin 11) :
    binaryValue (codeBit b i j) = codeMatrix b i j := rfl

/-- A checked evaluator for each published five-by-five minor. -/
def compoundBit (b : Bool) (i j : Fin 462) : Bool :=
  binaryDet 5 (fun k l => codeBit b (fiveTuple i k) (fiveTuple j l))

lemma binaryValue_compoundBit (b : Bool) (i j : Fin 462) :
    binaryValue (compoundBit b i j) = compoundMatrix (codeMatrix b) i j := by
  rw [compoundBit, binaryValue_binaryDet]
  rfl

lemma compoundMatrix_eq_of_bits (b : Bool)
    (h : ∀ i j : Fin 462, compoundBit b i j =
      ((if b then exteriorRowsB else exteriorRowsA)[i.val]!).testBit j.val) :
    compoundMatrix (codeMatrix b) = exteriorMatrix b := by
  ext i j
  rw [← binaryValue_compoundBit, h]
  rfl

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates

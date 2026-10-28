module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Evaluation


/-!
# Bitwise parallel Laplace expansion

A natural number packs several independent Boolean entries. XOR and AND
perform the characteristic-two determinant expansion in every bit position
simultaneously. The mask supplies the value one at each position being used.
`packedDet_testBit` connects this evaluator to the already proved `binaryDet`,
so no finite computation bypasses the determinant soundness theorem.

This is the arithmetic used to certify the native second generator's fifth
compound matrix. Source conventions: James, J. Algebra 27 (1973), 57–111;
GM02 Proposition 5.1; `NativeActions/source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second

/-- Simultaneous Boolean determinants, one in each bit of the natural number. -/
def packedDet (mask : ℕ) : (n : ℕ) → (Fin n → Fin n → ℕ) → ℕ
  | 0, _ => mask
  | n + 1, m => (List.ofFn (fun j : Fin (n + 1) =>
      m 0 j &&& packedDet mask n (fun k l => m k.succ (j.succAbove l)))).foldr Nat.xor 0

lemma testBit_fold (l : List ℕ) (j : ℕ) :
    (l.foldr Nat.xor 0).testBit j = (l.map (fun a => a.testBit j)).foldr Bool.xor false := by
  induction l with
  | nil => exact Nat.zero_testBit j
  | cons a l ih =>
    change (a ^^^ l.foldr Nat.xor 0).testBit j = _
    rw [Nat.testBit_xor, ih]
    rfl

/-- Taking a bit commutes with the entire Laplace expansion. -/
lemma packedDet_testBit (mask n : ℕ) (m : Fin n → Fin n → ℕ)
    (j : ℕ) (hj : mask.testBit j = true) :
    (packedDet mask n m).testBit j = binaryDet n (fun k l => (m k l).testBit j) := by
  induction n with
  | zero => exact hj
  | succ n ih =>
    rw [packedDet, testBit_fold, List.map_ofFn, binaryDet]
    congr 2
    funext q
    change (m 0 q &&& packedDet mask n (fun k l => m k.succ (q.succAbove l))).testBit j = _
    rw [Nat.testBit_and, ih]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second

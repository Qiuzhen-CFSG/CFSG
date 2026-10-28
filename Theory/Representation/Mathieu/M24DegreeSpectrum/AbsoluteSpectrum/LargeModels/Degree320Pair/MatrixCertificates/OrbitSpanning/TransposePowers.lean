module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.TransposeArithmetic

/-!
# Literal divisors for bounded transpose checks

The divisor doubles when moving to the next column. Its initial literal value
is checked once against the appropriate power of two. This prevents each entry
check from repeating that exponentiation. The final conclusion is the original
packed transpose checker, used by the degree-320 left orbit certificates.
Source and measurements: `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitCertificates
def transposePowers (a : List Nat) : Nat → List Nat → Bool
  | _, [] => true
  | d, c :: cs => (packedColumn d a == c) && transposePowers a (2*d) cs

theorem transposePowers_eq (a : List Nat) (i : Nat) (b : List Nat) :
    transposePowers a (2^i) b = transposeRows a i b := by
  induction b generalizing i with
  | nil => rfl
  | cons x xs ih =>
    simp only [transposePowers, transposeRows, checkColumn]
    rw [Nat.mul_comm 2 (2^i), ← pow_succ, ih]

theorem transposeRows_of_powers (a : List Nat) (i d : Nat) (b : List Nat)
    (hd : 2^i = d) (h : transposePowers a d b = true) : transposeRows a i b = true := by
  rw [← transposePowers_eq, hd]
  exact h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitCertificates

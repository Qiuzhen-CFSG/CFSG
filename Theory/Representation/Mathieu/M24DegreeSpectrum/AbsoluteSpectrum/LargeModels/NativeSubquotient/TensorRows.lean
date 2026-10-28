module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.TensorCoordinates
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Packed

/-!
# Packed coordinates for native tensor actions

The structural bit theorem identifies a packed tensor row with the Kronecker
product of the factor matrices. Its concrete consumer is the saved degree-320
embedding; the same literal row order is used for the two larger constituents.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient
open Degree220Pair.NativeActions.CertificatePacked Thompson.BinaryMatrix
open TensorCoordinates Packed

/-- Certify a whole tensor matrix by checking its packed rows and the bound on
one small factor, instead of checking every large-matrix entry separately. -/
theorem tensorMatrix_of_rows {m n : ℕ} (a b rows : List ℕ)
    (hb : ∀ i : Fin n, b[i.val]! < 2^n)
    (hc : ∀ i : Fin (m*n),
      tensorRow n m a[i.divNat.val]! b[i.modNat.val]! = rows[i.val]!) :
    tensorMatrix (matrix m m a) (matrix n n b) = matrix (m*n) (m*n) rows := by
  ext i j
  rw [tensorMatrix_apply]
  change bit a[i.divNat.val]! j.divNat.val * bit b[i.modNat.val]! j.modNat.val =
    bit rows[i.val]! j.val
  rw [← hc i]
  have ht := tensorRow_bit n m a[i.divNat.val]! b[i.modNat.val]!
    j.divNat.val j.modNat.val (hb i.modNat) j.divNat.isLt j.modNat.isLt
  have hj : j.divNat.val * n + j.modNat.val = j.val := Nat.div_add_mod' _ _
  rw [hj] at ht
  unfold bit
  rw [ht]
  cases a[i.divNat.val]!.testBit j.divNat.val <;>
    cases b[i.modNat.val]!.testBit j.modNat.val <;> simp

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient

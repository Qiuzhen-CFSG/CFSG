module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.FrameCertificate.InverseRows

/-!
# Interpreting the checked LeftInverse rows

The numerical row certificates are a separate cache boundary. This module
uses their proved equalities with the original packed matrix decoder.
Source: `Norm/source/README.md` and the unchanged constants in `Norm.Frame`.
-/

public section
open Matrix
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open FactorAlgebras.Certificate MatrixChecks
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm

private theorem identity_rows : matrix (n := 252) c0 = 1 := by
  have h : ∀ i : Fin 252, entry c0 i.val = 2 ^ i.val := by decide +kernel
  ext i j
  simp only [matrix, vector, h i, bit_power, Matrix.one_apply, Fin.val_inj]

/-- The inverse multiplies the frame on the left, as required for cancellation. -/
theorem frame_left_inverse : frameInverse * frame = 1 := by
  rw [frame_eq_take]
  exact (matrix_product (n := 252) inverseRows (orbitRows.take 252) c0
    (by decide +kernel)
    (product_rows inverseRows (orbitRows.take 252) c0 (by decide +kernel) FrameCertificate.inverse_rows)).trans
      identity_rows

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm

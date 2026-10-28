module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.FrameCertificate.GeneratorRows

/-!
# Interpreting the checked GeneratorProduct rows

The numerical row certificates are a separate cache boundary. This module
uses their proved equalities with the original packed matrix decoder.
Source: `Norm/source/README.md` and the unchanged constants in `Norm.Frame`.
-/

public section
open Matrix
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open FactorAlgebras.Certificate MatrixChecks
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm

/-- Node 3 is exactly the product of the two published generators, in this order. -/
theorem generatorProduct_eq : generatorProduct = matrix252 0 * matrix252 1 :=
  (matrix_product (n := 252) c1 c2 c3 (by decide +kernel)
    (product_rows c1 c2 c3 (by decide +kernel) FrameCertificate.generator_rows)).symm

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm

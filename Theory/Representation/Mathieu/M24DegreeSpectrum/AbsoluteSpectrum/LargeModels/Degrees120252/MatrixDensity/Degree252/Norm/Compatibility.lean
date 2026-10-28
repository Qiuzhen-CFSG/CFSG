module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.Frame
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.Compatibility.Left
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.Compatibility.Products
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.Compatibility.Seeds

/-!
# Compatibility of the degree-252 norm with the proposed frame

The literal node-19 matrix takes each of the eleven seeds to the sum of its
twenty-three stored rows, including the last, 253rd row. The checked
factorization `N = U V` through ten coordinates and the identities
`G U = U`, `V G = V` prove that
`G = matrix c3` commutes with `N = matrix c19` by associativity.

These unconditional identities require neither frame invertibility nor an
identification of node 3 with the original generator product. The applications
in `Compatibility.Consumer` discharge exactly these compatibility premises of
the existing
frame reduction and its density application. The remaining three finite frame
identities stay explicit for the independent frame-certificate producer.

Source: the unchanged `Degrees120252/source/density-252.json`, the original
packed matrices and `Norm.Frame`; see `Compatibility/source/README.md`.
-/

public section
open Matrix
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open FactorAlgebras.Certificate MatrixChecks
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252

namespace Norm
open CompatibilityChecks

/-- The literal generator-product candidate commutes with the literal norm. -/
theorem norm_commutes : generatorProduct * normMatrix = normMatrix * generatorProduct := by
  have hfactor : rect (m := 252) (n := 10) u20 * rect (n := 252) v20 = normMatrix :=
    rect_product u20 v20 c19 (by decide +kernel) (by decide +kernel) factor_rows
  have hleft : generatorProduct * rect (m := 252) (n := 10) u20 = rect u20 :=
    rect_product c3 u20 u20 (by decide +kernel) (by decide +kernel) left_rows
  have hright : rect (m := 10) (n := 252) v20 * generatorProduct = rect v20 :=
    rect_product v20 c3 v20 (by decide +kernel) (by decide +kernel) right_rows
  rw [← hfactor, ← Matrix.mul_assoc, hleft, Matrix.mul_assoc, hright]

end Norm

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252

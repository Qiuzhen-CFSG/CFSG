module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.Compatibility.Left.Lower
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.Compatibility.Left.Upper

/-!
# Join the checked halves of the fixed left factor

Concatenate the first 128 rows and the remaining 124 rows. The two checked
parts establish all of `c3 * U = U` without repeating any arithmetic.
Source: `Degrees120252/source/density-252.json`; see `source/README.md`.
-/

public section
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open MatrixChecks
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree120.Norm (append_rows)
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.CompatibilityChecks

theorem left_rows : c3.map (combineList u20) = u20 := by
  have h := append_rows left_lower left_upper
  simpa only [List.take_append_drop] using h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.CompatibilityChecks

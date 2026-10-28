module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.Data
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.Arithmetic

/-!
# Checked recombination of the two singular-expression parts

A sequential XOR check compares all 1792 packed rows, including every column,
with the fixed `SingularData.singularRows`. The two separate matrix-product
identities remain independent premises of the assembly in `SingularMatrix`.
See `source/README.md` for source attribution and certificate generation.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix

set_option maxRecDepth 8192 in
private theorem sum_checked :
    Wide.checkSum leftRows.toList rightRows.toList singularRows.toList = true := by
  decide +kernel

/-- The two proposed parts recombine to the *published* packed singular matrix. -/
theorem packedLeft_add_packedRight : packedLeft + packedRight = packedSingular := by
  have ha : leftRows.toList.length = 1792 := by decide +kernel
  exact Wide.sum_sound 1792 leftRows.toList rightRows.toList singularRows.toList ha sum_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix

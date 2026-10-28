module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product02A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.OrderData

/-!
# Reusing the certified square of the 320a second generator

The first product in the existing trace certificate is precisely Ba * Ba.
Its checked output equals the square candidate used by the presentation
certificates. This identifies the two literal data lists without recertifying
matrix multiplication. Source: the unchanged ATLAS degree-320a generator,
documented in `Degree320Pair/source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate

/-- The existing trace product certifies the same literal square candidate. -/
theorem SquareBA_checked : checkRows Data.BaRows Data.BaRows squareBaRows = true := by
  have hd : Data.R2aRows = squareBaRows := by decide +kernel
  rw [← hd]
  exact MatrixCertificates.TraceRows.r2a

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate

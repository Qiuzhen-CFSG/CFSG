module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.Inputs
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates.ProjectionSection
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates.ProjectionA
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates.ProjectionB
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates.DualInverse
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates.DualA
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates.DualB

/-!
# The native degree-220 quotient and dual matrix certificates

The seven identities are proved for the literal published matrices over F₂.
Packed XOR computations are kernel checked in bounded row batches; the
rectangular decoding theorems turn them into matrix products. The transpose
checks preserve the ATLAS row-action convention, and the reverse dual inverse
follows from the proved left inverse for finite square matrices.

These identities supply the matrix input to
`Degree220Pair.nativeRealizationsExist_of_exterior_and_certificates`. The
identification of the native exterior-power coordinates is an independent
input to that theorem, and is not assumed by these finite certificates.

Sources: James, J. Algebra 27 (1973), 57--111; GM02 Proposition 5.1.
Witness provenance: `source/README.md`; checked auxiliary transcription and
performance notes: `MatrixCertificates/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions

/-- The quotient is split surjective and intertwines both native exterior
matrices; the two degree-220 pairs are related by the specified dual change. -/
theorem matrixCertificates : MatrixCertificates where
  projection_section := CertificateChecks.projection_section
  projection_A := CertificateChecks.projection_A
  projection_B := CertificateChecks.projection_B
  dual_left := CertificateChecks.dual_left
  dual_right := CertificateChecks.dual_right
  dual_A := CertificateChecks.dual_A
  dual_B := CertificateChecks.dual_B

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions

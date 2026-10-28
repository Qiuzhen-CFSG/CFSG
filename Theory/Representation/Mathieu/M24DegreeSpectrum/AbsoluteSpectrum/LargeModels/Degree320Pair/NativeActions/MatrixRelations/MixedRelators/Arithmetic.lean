module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Arithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.Blocks

/-!
# Sparse checks with an inert assembly boundary

The proved gap checker computes XOR sums of selected rows and reconstructs
the literal input masks. Packaging its conclusion in `Checked` allows the
shared block assembly to join certificates without unfolding a whole closed
matrix multiplication during type conversion. The concrete consumers are the
thirty product certificates for the mixed ATLAS relators in this directory.

Source: John Bray, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/M24G1-P1.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate.MixedRelators

/-- Sound sparse arithmetic, packaged for the existing symbolic block joins. -/
theorem of_gaps (a b c : List Nat) (gs : List (List Nat))
    (h : MatrixCertificates.TraceRows.checkGaps a b c gs = true) : Checked a b c :=
  ⟨MatrixCertificates.checkRows_of_skip a b c
    (MatrixCertificates.TraceRows.checkGaps_sound a b c gs h)⟩

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate.MixedRelators

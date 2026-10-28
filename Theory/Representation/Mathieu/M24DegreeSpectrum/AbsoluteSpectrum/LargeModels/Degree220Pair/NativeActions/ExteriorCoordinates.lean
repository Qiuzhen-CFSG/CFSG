module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Evaluation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.First
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second

/-!
# Native fifth-exterior coordinates

The imported construction gives a linear equivalence from the actual fifth
exterior power of `MathieuCode.Code` to 462 coordinates and proves its exact
compound-matrix action at both native generators. The two independently checked
finite comparisons identify these compound matrices with the published exterior
matrices. Combining them proves `nonempty_exteriorCoordinates` without any
degree-220 action, irreducibility, presentation or spectrum premise.

Sources: James, J. Algebra 27 (1973), 57–111; GM02 Proposition 5.1;
`NativeActions/source/README.md` for native labels and column conventions.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions

/-- Apply the genuine exterior-coordinate construction to the two literal minor identities. -/
theorem nonempty_exteriorCoordinates_of_compoundCertificates
    (h : ExteriorCoordinates.CompoundCertificates) : Nonempty ExteriorCoordinates :=
  ⟨ExteriorCoordinates.of_compoundCertificates h⟩

/-- The genuine fifth exterior power has the two prescribed native generator matrices. -/
theorem nonempty_exteriorCoordinates : Nonempty ExteriorCoordinates := by
  apply nonempty_exteriorCoordinates_of_compoundCertificates
  intro b
  cases b
  · exact ExteriorCoordinates.compoundMatrix_first
  · exact ExteriorCoordinates.compoundMatrix_second

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions

module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.CertificateInput
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.TransposeCertificates.A
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences.TransposeCertificates.B

/-!
# All literal transpose comparisons for the column orbit

The 88 kernel-checked blocks compare all 2816 proposed transpose rows with the
original two matrices. The append assembly proves the exact `TransposeChecks`
contract consumed by `Cyclicity.columnOrbitRecurrences_of_checks`. The independent
product certificate is left to that consumer's assembly owner.

Source tables, attribution and bit conventions: `ColumnRecurrences/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences

/-- Both proposed transpose tables agree with every column of the literal matrices. -/
theorem transposeChecks : TransposeChecks :=
  ⟨transposeARows_check, transposeBRows_check⟩

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnRecurrences

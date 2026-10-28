module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.One
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.LiteralProducts

/-! Identification of the commutator circuit inputs with the unchanged
ATLAS arrays, and of its output with the identity matrix.
Source and conventions: `source/README.md`. -/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Sources

set_option maxRecDepth 8192 in
theorem first_rows : Data.a.rows = Data1242.firstRows.toList := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem second_rows : Data.b.rows = Data1242.secondRows.toList := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem identity_rows : Data.one.rows = identityRows 1242 := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Sources

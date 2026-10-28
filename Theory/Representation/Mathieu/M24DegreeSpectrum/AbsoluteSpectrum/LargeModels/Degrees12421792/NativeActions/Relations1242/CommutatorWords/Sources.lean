module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.SourceRows

/-! Identification of the commutator circuit inputs with the unchanged
ATLAS arrays, and of its output with the identity matrix.
Source and conventions: `source/README.md`. -/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Sources
theorem first_matrix : Data.a.matrix = Data1242.first := by
  simp only [Data.a.matrix, first_rows, Array.toArray_toList, Data1242.first]

theorem second_matrix : Data.b.matrix = Data1242.second := by
  simp only [Data.b.matrix, second_rows, Array.toArray_toList, Data1242.second]

theorem identity_matrix : Data.one.matrix = 1 := by
  simpa only [Data.one.matrix, identity_rows] using decode_identityRows 1242
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Sources

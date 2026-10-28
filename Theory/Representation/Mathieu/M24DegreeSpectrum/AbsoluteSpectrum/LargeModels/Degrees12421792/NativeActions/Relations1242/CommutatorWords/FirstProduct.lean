module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Sources
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Blocks
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FirstChecks0
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FirstChecks1
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FirstChecks2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FirstChecks3

/-! The complete first product in the degree-1242 commutator circuit.
The actual-source comparison is supplied by `Sources`. See `source/README.md`. -/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FirstProduct
theorem checked : checkChunks Data.a.blocks Data.b.rows Data.x.blocks Data.a.hints = true := by
  simp only [Data.a.blocks, Data.x.blocks, Data.a.hints, checkChunks, Bool.and_eq_true]
  exact ⟨checked00, checked01, checked02, checked03, checked04, checked05, checked06, checked07, checked08, checked09, checked10, checked11, checked12, checked13, checked14, checked15, checked16, checked17, checked18, checked19, checked20, checked21, checked22, checked23, checked24, checked25, checked26, checked27, checked28, checked29, checked30, checked31, checked32, checked33, checked34, checked35, checked36, checked37, checked38, checked39, checked40, checked41, checked42, checked43, checked44, checked45, True.intro⟩

theorem matrix_product : Data.a.matrix * Data.b.matrix = Data.x.matrix :=
  product_of_chunks _ _ _ _ Data.a.length_rows Data.b.length_rows checked
/-- This is the product of the actual, untransposed ATLAS arrays. -/
theorem literal_product : Data1242.first * Data1242.second = Data.x.matrix := by
  rw [← Sources.first_matrix, ← Sources.second_matrix]
  exact matrix_product
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FirstProduct

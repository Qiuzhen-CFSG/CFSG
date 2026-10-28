module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Circuit
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.TwelfthPower.Square
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.TwelfthPower.Cube
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.TwelfthPower.Sixth
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.TwelfthPower.Twelfth

/-! The twelfth power of the fixed untransposed degree-1242 commutator matrix.
Four completely checked products give w², w³, w⁶ and w¹² = 1.
The original positive ATLAS word follows under just its two independent
prefix equations; the parent commutator assembly discharges those premises.
Source: John Bray, ATLAS M24G1-P1; see `TwelfthPower/source/README.md`. -/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.TwelfthPower
theorem twelfth_power : Data.w.matrix ^ 12 = 1 :=
  twelfth_of_products Square.matrix_product Cube.matrix_product
    Sixth.matrix_product Twelfth.matrix_product

theorem commutator_order12_of_prefix_products
    (hy : Data.x.matrix * Data.b.matrix = Data.y.matrix)
    (hw : Data.y.matrix * Data.x.matrix = Data.w.matrix) :
    (Data1242.first * Data1242.second^2 * Data1242.first * Data1242.second)^12 = 1 := by
  rw [wordThree_eq hy hw]
  exact twelfth_power

theorem third_source_word_of_prefix_products
    (hy : Data.x.matrix * Data.b.matrix = Data.y.matrix)
    (hw : Data.y.matrix * Data.x.matrix = Data.w.matrix) :
    Presentation.rowRelatorValues Data1242.first Data1242.second 3 = 1 := by
  simpa [Presentation.rowRelatorValues] using
    commutator_order12_of_prefix_products hy hw
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.TwelfthPower

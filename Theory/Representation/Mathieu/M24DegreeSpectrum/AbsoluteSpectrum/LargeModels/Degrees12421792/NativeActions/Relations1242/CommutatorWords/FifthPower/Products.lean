module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks00
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks01
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks02
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks03
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks04
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks05
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks06
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks07

/-! The three complete numerical products for the fifth power. Every lookup table
and every row is kernel checked, in the literal untransposed convention.
See `source/README.md`. -/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Products
theorem square_checked : Arithmetic.chunksCheck 6 1242 TablesV.tables
    Data.v.blocks Data.v2.blocks = true := by
  simp only [Data.v.blocks, Data.v2.blocks, Arithmetic.chunksCheck, Bool.and_eq_true]
  exact ⟨Checks.square00, Checks.square01, Checks.square02, Checks.square03, Checks.square04, Checks.square05, Checks.square06, Checks.square07, Checks.square08, Checks.square09, Checks.square10, Checks.square11, Checks.square12, Checks.square13, Checks.square14, Checks.square15, Checks.square16, Checks.square17, Checks.square18, Checks.square19, Checks.square20, Checks.square21, Checks.square22, Checks.square23, Checks.square24, Checks.square25, Checks.square26, Checks.square27, Checks.square28, Checks.square29, Checks.square30, Checks.square31, Checks.square32, Checks.square33, Checks.square34, Checks.square35, Checks.square36, Checks.square37, Checks.square38, Checks.square39, Checks.square40, Checks.square41, Checks.square42, Checks.square43, Checks.square44, Checks.square45, True.intro⟩

theorem square : Data.v.matrix * Data.v.matrix = Data.v2.matrix := by
  have hb : TablesV.inputs.flatten.length = 1242 := by
    rw [TablesV.input_rows]
    exact Data.v.length_rows
  have h := Arithmetic.product_chunks 1242 6 1242 Data.v.blocks Data.v2.blocks
    TablesV.inputs TablesV.tables Data.v.length_rows hb TablesV.checked square_checked
  simpa only [TablesV.input_rows, Data.v.matrix, Data.v.rows,
    Data.v2.matrix, Data.v2.rows] using h

theorem fourth_checked : Arithmetic.chunksCheck 6 1242 TablesV2.tables
    Data.v2.blocks Data.v4.blocks = true := by
  simp only [Data.v2.blocks, Data.v4.blocks, Arithmetic.chunksCheck, Bool.and_eq_true]
  exact ⟨Checks.fourth00, Checks.fourth01, Checks.fourth02, Checks.fourth03, Checks.fourth04, Checks.fourth05, Checks.fourth06, Checks.fourth07, Checks.fourth08, Checks.fourth09, Checks.fourth10, Checks.fourth11, Checks.fourth12, Checks.fourth13, Checks.fourth14, Checks.fourth15, Checks.fourth16, Checks.fourth17, Checks.fourth18, Checks.fourth19, Checks.fourth20, Checks.fourth21, Checks.fourth22, Checks.fourth23, Checks.fourth24, Checks.fourth25, Checks.fourth26, Checks.fourth27, Checks.fourth28, Checks.fourth29, Checks.fourth30, Checks.fourth31, Checks.fourth32, Checks.fourth33, Checks.fourth34, Checks.fourth35, Checks.fourth36, Checks.fourth37, Checks.fourth38, Checks.fourth39, Checks.fourth40, Checks.fourth41, Checks.fourth42, Checks.fourth43, Checks.fourth44, Checks.fourth45, True.intro⟩

theorem fourth : Data.v2.matrix * Data.v2.matrix = Data.v4.matrix := by
  have hb : TablesV2.inputs.flatten.length = 1242 := by
    rw [TablesV2.input_rows]
    exact Data.v2.length_rows
  have h := Arithmetic.product_chunks 1242 6 1242 Data.v2.blocks Data.v4.blocks
    TablesV2.inputs TablesV2.tables Data.v2.length_rows hb TablesV2.checked fourth_checked
  simpa only [TablesV2.input_rows, Data.v2.matrix, Data.v2.rows,
    Data.v4.matrix, Data.v4.rows] using h

theorem final_product_checked : Arithmetic.chunksCheck 6 1242 TablesV.tables
    Data.v4.blocks Data.one.blocks = true := by
  simp only [Data.v4.blocks, Data.one.blocks, Arithmetic.chunksCheck, Bool.and_eq_true]
  exact ⟨Checks.final00, Checks.final01, Checks.final02, Checks.final03, Checks.final04, Checks.final05, Checks.final06, Checks.final07, Checks.final08, Checks.final09, Checks.final10, Checks.final11, Checks.final12, Checks.final13, Checks.final14, Checks.final15, Checks.final16, Checks.final17, Checks.final18, Checks.final19, Checks.final20, Checks.final21, Checks.final22, Checks.final23, Checks.final24, Checks.final25, Checks.final26, Checks.final27, Checks.final28, Checks.final29, Checks.final30, Checks.final31, Checks.final32, Checks.final33, Checks.final34, Checks.final35, Checks.final36, Checks.final37, Checks.final38, Checks.final39, Checks.final40, Checks.final41, Checks.final42, Checks.final43, Checks.final44, Checks.final45, True.intro⟩

theorem final_product : Data.v4.matrix * Data.v.matrix = Data.one.matrix := by
  have hb : TablesV.inputs.flatten.length = 1242 := by
    rw [TablesV.input_rows]
    exact Data.v.length_rows
  have h := Arithmetic.product_chunks 1242 6 1242 Data.v4.blocks Data.one.blocks
    TablesV.inputs TablesV.tables Data.v4.length_rows hb TablesV.checked final_product_checked
  simpa only [TablesV.input_rows, Data.v4.matrix, Data.v4.rows,
    Data.v.matrix, Data.v.rows, Data.one.matrix, Data.one.rows] using h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Products

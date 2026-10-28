module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.TablesV
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.TablesV2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.V4
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.One

/-! Kernel certificates for the three numerical power products. See `source/README.md`. -/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks
set_option maxRecDepth 8192 in
theorem square06 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block06 Data.v2.block06 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem fourth06 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block06 Data.v4.block06 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem final06 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block06 Data.one.block06 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem square07 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block07 Data.v2.block07 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem fourth07 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block07 Data.v4.block07 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem final07 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block07 Data.one.block07 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem square08 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block08 Data.v2.block08 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem fourth08 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block08 Data.v4.block08 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem final08 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block08 Data.one.block08 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem square09 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block09 Data.v2.block09 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem fourth09 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block09 Data.v4.block09 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem final09 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block09 Data.one.block09 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem square10 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block10 Data.v2.block10 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem fourth10 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block10 Data.v4.block10 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem final10 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block10 Data.one.block10 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem square11 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block11 Data.v2.block11 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem fourth11 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block11 Data.v4.block11 = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem final11 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block11 Data.one.block11 = true := by decide +kernel
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks

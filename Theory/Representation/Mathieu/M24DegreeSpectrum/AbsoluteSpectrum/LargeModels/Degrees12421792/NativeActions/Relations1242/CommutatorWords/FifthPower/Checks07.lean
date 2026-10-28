module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Sparse
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.TablesV
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.TablesV2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.V4
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Data.One

/-! Kernel certificates for the three numerical power products. See `source/README.md`. -/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks
-- Serialize these numerical declarations after the measured memory comparison.
set_option Elab.async false

set_option maxRecDepth 8192 in
theorem square42 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block42 Data.v2.block42 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth42 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block42 Data.v4.block42 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final42 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block42 Data.one.block42 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square43 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block43 Data.v2.block43 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth43 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block43 Data.v4.block43 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final43 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block43 Data.one.block43 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square44 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block44 Data.v2.block44 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth44 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block44 Data.v4.block44 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final44 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block44 Data.one.block44 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square45 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block45 Data.v2.block45 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth45 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block45 Data.v4.block45 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final45 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block45 Data.one.block45 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks

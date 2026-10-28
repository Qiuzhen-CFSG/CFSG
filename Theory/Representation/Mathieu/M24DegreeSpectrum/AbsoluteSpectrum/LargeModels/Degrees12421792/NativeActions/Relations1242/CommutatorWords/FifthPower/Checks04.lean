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
theorem square24 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block24 Data.v2.block24 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth24 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block24 Data.v4.block24 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final24 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block24 Data.one.block24 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square25 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block25 Data.v2.block25 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth25 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block25 Data.v4.block25 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final25 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block25 Data.one.block25 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square26 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block26 Data.v2.block26 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth26 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block26 Data.v4.block26 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final26 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block26 Data.one.block26 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square27 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block27 Data.v2.block27 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth27 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block27 Data.v4.block27 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final27 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block27 Data.one.block27 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square28 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block28 Data.v2.block28 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth28 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block28 Data.v4.block28 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final28 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block28 Data.one.block28 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square29 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block29 Data.v2.block29 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth29 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block29 Data.v4.block29 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final29 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block29 Data.one.block29 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks

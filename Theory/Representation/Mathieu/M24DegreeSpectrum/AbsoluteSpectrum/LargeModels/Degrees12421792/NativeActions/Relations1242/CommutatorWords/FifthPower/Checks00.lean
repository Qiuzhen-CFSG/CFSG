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
theorem square00 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block00 Data.v2.block00 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth00 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block00 Data.v4.block00 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final00 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block00 Data.one.block00 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square01 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block01 Data.v2.block01 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth01 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block01 Data.v4.block01 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final01 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block01 Data.one.block01 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square02 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block02 Data.v2.block02 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth02 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block02 Data.v4.block02 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final02 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block02 Data.one.block02 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square03 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block03 Data.v2.block03 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth03 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block03 Data.v4.block03 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final03 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block03 Data.one.block03 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square04 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block04 Data.v2.block04 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth04 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block04 Data.v4.block04 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final04 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block04 Data.one.block04 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square05 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block05 Data.v2.block05 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth05 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block05 Data.v4.block05 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final05 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block05 Data.one.block05 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks

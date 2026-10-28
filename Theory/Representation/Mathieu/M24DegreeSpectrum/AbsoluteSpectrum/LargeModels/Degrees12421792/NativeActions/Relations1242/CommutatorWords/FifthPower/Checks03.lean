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
theorem square18 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block18 Data.v2.block18 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth18 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block18 Data.v4.block18 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final18 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block18 Data.one.block18 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square19 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block19 Data.v2.block19 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth19 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block19 Data.v4.block19 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final19 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block19 Data.one.block19 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square20 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block20 Data.v2.block20 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth20 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block20 Data.v4.block20 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final20 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block20 Data.one.block20 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square21 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block21 Data.v2.block21 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth21 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block21 Data.v4.block21 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final21 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block21 Data.one.block21 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square22 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block22 Data.v2.block22 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth22 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block22 Data.v4.block22 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final22 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block22 Data.one.block22 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square23 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block23 Data.v2.block23 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth23 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block23 Data.v4.block23 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final23 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block23 Data.one.block23 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks

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
theorem square12 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block12 Data.v2.block12 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth12 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block12 Data.v4.block12 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final12 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block12 Data.one.block12 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square13 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block13 Data.v2.block13 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth13 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block13 Data.v4.block13 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final13 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block13 Data.one.block13 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square14 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block14 Data.v2.block14 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth14 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block14 Data.v4.block14 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final14 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block14 Data.one.block14 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square15 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block15 Data.v2.block15 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth15 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block15 Data.v4.block15 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final15 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block15 Data.one.block15 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square16 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block16 Data.v2.block16 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth16 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block16 Data.v4.block16 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final16 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block16 Data.one.block16 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem square17 : Arithmetic.check 6 1242 TablesV.tables
    Data.v.block17 Data.v2.block17 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem fourth17 : Arithmetic.check 6 1242 TablesV2.tables
    Data.v2.block17 Data.v4.block17 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v2_zeros
  decide +kernel
set_option maxRecDepth 8192 in
theorem final17 : Arithmetic.check 6 1242 TablesV.tables
    Data.v4.block17 Data.one.block17 = true := by
  apply Sparse.check_sound _ _ _ Sparse.v_zeros
  decide +kernel
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Checks

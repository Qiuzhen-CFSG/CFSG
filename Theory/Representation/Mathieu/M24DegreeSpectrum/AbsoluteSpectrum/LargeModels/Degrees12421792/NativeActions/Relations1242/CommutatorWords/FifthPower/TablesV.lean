module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.TablesV.Entries

/-! Assembly of all checked lookup tables and their complete input-row bridge. See `source/README.md`. -/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.TablesV
theorem checked : Arithmetic.tablesCheck 6 1242 inputs tables = true := by
  unfold inputs tables
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked00
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked01
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked02
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked03
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked04
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked05
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked06
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked07
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked08
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked09
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked10
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked11
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked12
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked13
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked14
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked15
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked16
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked17
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked18
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked19
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked20
  apply Arithmetic.tablesCheck_append _ _ _ _ _ _ checked21
  exact checked22
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.TablesV

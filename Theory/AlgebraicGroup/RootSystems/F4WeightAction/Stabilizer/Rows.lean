module
public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.Stabilizer.Verifier

/-! The complete 1,152-element arithmetic census, in 24 rows of 48 elements.
A representative row was measured first. Declaration elaboration is serialized
here because parallel kernel reductions duplicate the same table and increase
peak memory; the project thread settings are unchanged. -/
set_option Elab.async false
public noncomputable section
namespace Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction.Stabilizer.Rows
open Verifier

private theorem checked00 : rowOK 0 = true := by decide +kernel

private theorem checked01 : rowOK 1 = true := by decide +kernel

private theorem checked02 : rowOK 2 = true := by decide +kernel

private theorem checked03 : rowOK 3 = true := by decide +kernel

private theorem checked04 : rowOK 4 = true := by decide +kernel

private theorem checked05 : rowOK 5 = true := by decide +kernel

private theorem checked06 : rowOK 6 = true := by decide +kernel

private theorem checked07 : rowOK 7 = true := by decide +kernel

private theorem checked08 : rowOK 8 = true := by decide +kernel

private theorem checked09 : rowOK 9 = true := by decide +kernel

private theorem checked10 : rowOK 10 = true := by decide +kernel

private theorem checked11 : rowOK 11 = true := by decide +kernel

private theorem checked12 : rowOK 12 = true := by decide +kernel

private theorem checked13 : rowOK 13 = true := by decide +kernel

private theorem checked14 : rowOK 14 = true := by decide +kernel

private theorem checked15 : rowOK 15 = true := by decide +kernel

private theorem checked16 : rowOK 16 = true := by decide +kernel

private theorem checked17 : rowOK 17 = true := by decide +kernel

private theorem checked18 : rowOK 18 = true := by decide +kernel

private theorem checked19 : rowOK 19 = true := by decide +kernel

private theorem checked20 : rowOK 20 = true := by decide +kernel

private theorem checked21 : rowOK 21 = true := by decide +kernel

private theorem checked22 : rowOK 22 = true := by decide +kernel

private theorem checked23 : rowOK 23 = true := by decide +kernel

theorem checked (a : Fin 24) : rowOK a = true := by
  fin_cases a
  · exact checked00
  · exact checked01
  · exact checked02
  · exact checked03
  · exact checked04
  · exact checked05
  · exact checked06
  · exact checked07
  · exact checked08
  · exact checked09
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17
  · exact checked18
  · exact checked19
  · exact checked20
  · exact checked21
  · exact checked22
  · exact checked23


end Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction.Stabilizer.Rows

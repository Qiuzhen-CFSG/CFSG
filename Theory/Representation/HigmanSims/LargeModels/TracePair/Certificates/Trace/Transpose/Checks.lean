module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Transpose.Blocks
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Data
import Mathlib.Tactic.FinCases

/-!
# Kernel checks of all 49 HS transpose blocks

Every certificate checks both coefficient planes of one 128-by-128 block
against the unchanged `generatorRowsB` and `columnsB`. The 49 certificates
cover all 896 rows and columns. Only kernel reduction is used; no downloaded
value or external calculation supplies a proof. See `source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Transpose

private theorem block00_checked : checkBlock generatorRowsB columnsB 0 0 = true := by
  decide +kernel

private theorem block01_checked : checkBlock generatorRowsB columnsB 0 1 = true := by
  decide +kernel

private theorem block02_checked : checkBlock generatorRowsB columnsB 0 2 = true := by
  decide +kernel

private theorem block03_checked : checkBlock generatorRowsB columnsB 0 3 = true := by
  decide +kernel

private theorem block04_checked : checkBlock generatorRowsB columnsB 0 4 = true := by
  decide +kernel

private theorem block05_checked : checkBlock generatorRowsB columnsB 0 5 = true := by
  decide +kernel

private theorem block06_checked : checkBlock generatorRowsB columnsB 0 6 = true := by
  decide +kernel

private theorem block10_checked : checkBlock generatorRowsB columnsB 1 0 = true := by
  decide +kernel

private theorem block11_checked : checkBlock generatorRowsB columnsB 1 1 = true := by
  decide +kernel

private theorem block12_checked : checkBlock generatorRowsB columnsB 1 2 = true := by
  decide +kernel

private theorem block13_checked : checkBlock generatorRowsB columnsB 1 3 = true := by
  decide +kernel

private theorem block14_checked : checkBlock generatorRowsB columnsB 1 4 = true := by
  decide +kernel

private theorem block15_checked : checkBlock generatorRowsB columnsB 1 5 = true := by
  decide +kernel

private theorem block16_checked : checkBlock generatorRowsB columnsB 1 6 = true := by
  decide +kernel

private theorem block20_checked : checkBlock generatorRowsB columnsB 2 0 = true := by
  decide +kernel

private theorem block21_checked : checkBlock generatorRowsB columnsB 2 1 = true := by
  decide +kernel

private theorem block22_checked : checkBlock generatorRowsB columnsB 2 2 = true := by
  decide +kernel

private theorem block23_checked : checkBlock generatorRowsB columnsB 2 3 = true := by
  decide +kernel

private theorem block24_checked : checkBlock generatorRowsB columnsB 2 4 = true := by
  decide +kernel

private theorem block25_checked : checkBlock generatorRowsB columnsB 2 5 = true := by
  decide +kernel

private theorem block26_checked : checkBlock generatorRowsB columnsB 2 6 = true := by
  decide +kernel

private theorem block30_checked : checkBlock generatorRowsB columnsB 3 0 = true := by
  decide +kernel

private theorem block31_checked : checkBlock generatorRowsB columnsB 3 1 = true := by
  decide +kernel

private theorem block32_checked : checkBlock generatorRowsB columnsB 3 2 = true := by
  decide +kernel

private theorem block33_checked : checkBlock generatorRowsB columnsB 3 3 = true := by
  decide +kernel

private theorem block34_checked : checkBlock generatorRowsB columnsB 3 4 = true := by
  decide +kernel

private theorem block35_checked : checkBlock generatorRowsB columnsB 3 5 = true := by
  decide +kernel

private theorem block36_checked : checkBlock generatorRowsB columnsB 3 6 = true := by
  decide +kernel

private theorem block40_checked : checkBlock generatorRowsB columnsB 4 0 = true := by
  decide +kernel

private theorem block41_checked : checkBlock generatorRowsB columnsB 4 1 = true := by
  decide +kernel

private theorem block42_checked : checkBlock generatorRowsB columnsB 4 2 = true := by
  decide +kernel

private theorem block43_checked : checkBlock generatorRowsB columnsB 4 3 = true := by
  decide +kernel

private theorem block44_checked : checkBlock generatorRowsB columnsB 4 4 = true := by
  decide +kernel

private theorem block45_checked : checkBlock generatorRowsB columnsB 4 5 = true := by
  decide +kernel

private theorem block46_checked : checkBlock generatorRowsB columnsB 4 6 = true := by
  decide +kernel

private theorem block50_checked : checkBlock generatorRowsB columnsB 5 0 = true := by
  decide +kernel

private theorem block51_checked : checkBlock generatorRowsB columnsB 5 1 = true := by
  decide +kernel

private theorem block52_checked : checkBlock generatorRowsB columnsB 5 2 = true := by
  decide +kernel

private theorem block53_checked : checkBlock generatorRowsB columnsB 5 3 = true := by
  decide +kernel

private theorem block54_checked : checkBlock generatorRowsB columnsB 5 4 = true := by
  decide +kernel

private theorem block55_checked : checkBlock generatorRowsB columnsB 5 5 = true := by
  decide +kernel

private theorem block56_checked : checkBlock generatorRowsB columnsB 5 6 = true := by
  decide +kernel

private theorem block60_checked : checkBlock generatorRowsB columnsB 6 0 = true := by
  decide +kernel

private theorem block61_checked : checkBlock generatorRowsB columnsB 6 1 = true := by
  decide +kernel

private theorem block62_checked : checkBlock generatorRowsB columnsB 6 2 = true := by
  decide +kernel

private theorem block63_checked : checkBlock generatorRowsB columnsB 6 3 = true := by
  decide +kernel

private theorem block64_checked : checkBlock generatorRowsB columnsB 6 4 = true := by
  decide +kernel

private theorem block65_checked : checkBlock generatorRowsB columnsB 6 5 = true := by
  decide +kernel

private theorem block66_checked : checkBlock generatorRowsB columnsB 6 6 = true := by
  decide +kernel

/-- Both planes of every block agree with the transposed candidate block. -/
theorem blocks_checked (r s : Fin 7) : checkBlock generatorRowsB columnsB r.val s.val = true := by
  fin_cases r <;> fin_cases s
  · exact block00_checked
  · exact block01_checked
  · exact block02_checked
  · exact block03_checked
  · exact block04_checked
  · exact block05_checked
  · exact block06_checked
  · exact block10_checked
  · exact block11_checked
  · exact block12_checked
  · exact block13_checked
  · exact block14_checked
  · exact block15_checked
  · exact block16_checked
  · exact block20_checked
  · exact block21_checked
  · exact block22_checked
  · exact block23_checked
  · exact block24_checked
  · exact block25_checked
  · exact block26_checked
  · exact block30_checked
  · exact block31_checked
  · exact block32_checked
  · exact block33_checked
  · exact block34_checked
  · exact block35_checked
  · exact block36_checked
  · exact block40_checked
  · exact block41_checked
  · exact block42_checked
  · exact block43_checked
  · exact block44_checked
  · exact block45_checked
  · exact block46_checked
  · exact block50_checked
  · exact block51_checked
  · exact block52_checked
  · exact block53_checked
  · exact block54_checked
  · exact block55_checked
  · exact block56_checked
  · exact block60_checked
  · exact block61_checked
  · exact block62_checked
  · exact block63_checked
  · exact block64_checked
  · exact block65_checked
  · exact block66_checked

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Transpose

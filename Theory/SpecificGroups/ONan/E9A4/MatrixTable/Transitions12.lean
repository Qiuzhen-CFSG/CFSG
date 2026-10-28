module

public import Theory.SpecificGroups.ONan.E9A4.MatrixTable.Checker
import Mathlib.Tactic.FinCases

/-!
# Checked transitions for a fixed E₉ coordinate

The 48 right-generator products in this slice are certified by the sound
GF(7) dot-product checker. The scalar is on the right. Data and ATLAS
attribution: `../source/README.md`; coordinate conventions: `E9A4Words.lean`.
-/

-- Keep the finite certificates sequential within each build unit.
set_option Elab.async false

namespace ONan.E9A4.MatrixTable
open Theory.SpecificGroups.E9A4 (next)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_60_0 : Data.m60 * Data.gen0 = (4 : ZMod 7) • Data.m96 := by
  unfold Data.m60 Data.gen0 Data.m96
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_60_1 : Data.m60 * Data.gen1 = (1 : ZMod 7) • Data.m36 := by
  unfold Data.m60 Data.gen1 Data.m36
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_60_2 : Data.m60 * Data.gen2 = (1 : ZMod 7) • Data.m61 := by
  unfold Data.m60 Data.gen2 Data.m61
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_60_3 : Data.m60 * Data.gen3 = (1 : ZMod 7) • Data.m62 := by
  unfold Data.m60 Data.gen3 Data.m62
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_61_0 : Data.m61 * Data.gen0 = (4 : ZMod 7) • Data.m97 := by
  unfold Data.m61 Data.gen0 Data.m97
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_61_1 : Data.m61 * Data.gen1 = (1 : ZMod 7) • Data.m37 := by
  unfold Data.m61 Data.gen1 Data.m37
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_61_2 : Data.m61 * Data.gen2 = (4 : ZMod 7) • Data.m60 := by
  unfold Data.m61 Data.gen2 Data.m60
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_61_3 : Data.m61 * Data.gen3 = (1 : ZMod 7) • Data.m63 := by
  unfold Data.m61 Data.gen3 Data.m63
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_62_0 : Data.m62 * Data.gen0 = (4 : ZMod 7) • Data.m98 := by
  unfold Data.m62 Data.gen0 Data.m98
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_62_1 : Data.m62 * Data.gen1 = (1 : ZMod 7) • Data.m38 := by
  unfold Data.m62 Data.gen1 Data.m38
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_62_2 : Data.m62 * Data.gen2 = (1 : ZMod 7) • Data.m64 := by
  unfold Data.m62 Data.gen2 Data.m64
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_62_3 : Data.m62 * Data.gen3 = (1 : ZMod 7) • Data.m65 := by
  unfold Data.m62 Data.gen3 Data.m65
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_63_0 : Data.m63 * Data.gen0 = (4 : ZMod 7) • Data.m99 := by
  unfold Data.m63 Data.gen0 Data.m99
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_63_1 : Data.m63 * Data.gen1 = (1 : ZMod 7) • Data.m39 := by
  unfold Data.m63 Data.gen1 Data.m39
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_63_2 : Data.m63 * Data.gen2 = (1 : ZMod 7) • Data.m66 := by
  unfold Data.m63 Data.gen2 Data.m66
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_63_3 : Data.m63 * Data.gen3 = (1 : ZMod 7) • Data.m67 := by
  unfold Data.m63 Data.gen3 Data.m67
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_64_0 : Data.m64 * Data.gen0 = (4 : ZMod 7) • Data.m100 := by
  unfold Data.m64 Data.gen0 Data.m100
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_64_1 : Data.m64 * Data.gen1 = (1 : ZMod 7) • Data.m40 := by
  unfold Data.m64 Data.gen1 Data.m40
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_64_2 : Data.m64 * Data.gen2 = (4 : ZMod 7) • Data.m62 := by
  unfold Data.m64 Data.gen2 Data.m62
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_64_3 : Data.m64 * Data.gen3 = (1 : ZMod 7) • Data.m68 := by
  unfold Data.m64 Data.gen3 Data.m68
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_65_0 : Data.m65 * Data.gen0 = (4 : ZMod 7) • Data.m101 := by
  unfold Data.m65 Data.gen0 Data.m101
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_65_1 : Data.m65 * Data.gen1 = (1 : ZMod 7) • Data.m41 := by
  unfold Data.m65 Data.gen1 Data.m41
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_65_2 : Data.m65 * Data.gen2 = (1 : ZMod 7) • Data.m69 := by
  unfold Data.m65 Data.gen2 Data.m69
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_65_3 : Data.m65 * Data.gen3 = (1 : ZMod 7) • Data.m60 := by
  unfold Data.m65 Data.gen3 Data.m60
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_66_0 : Data.m66 * Data.gen0 = (4 : ZMod 7) • Data.m102 := by
  unfold Data.m66 Data.gen0 Data.m102
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_66_1 : Data.m66 * Data.gen1 = (1 : ZMod 7) • Data.m42 := by
  unfold Data.m66 Data.gen1 Data.m42
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_66_2 : Data.m66 * Data.gen2 = (4 : ZMod 7) • Data.m63 := by
  unfold Data.m66 Data.gen2 Data.m63
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_66_3 : Data.m66 * Data.gen3 = (2 : ZMod 7) • Data.m69 := by
  unfold Data.m66 Data.gen3 Data.m69
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_67_0 : Data.m67 * Data.gen0 = (4 : ZMod 7) • Data.m103 := by
  unfold Data.m67 Data.gen0 Data.m103
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_67_1 : Data.m67 * Data.gen1 = (1 : ZMod 7) • Data.m43 := by
  unfold Data.m67 Data.gen1 Data.m43
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_67_2 : Data.m67 * Data.gen2 = (2 : ZMod 7) • Data.m68 := by
  unfold Data.m67 Data.gen2 Data.m68
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_67_3 : Data.m67 * Data.gen3 = (1 : ZMod 7) • Data.m61 := by
  unfold Data.m67 Data.gen3 Data.m61
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_68_0 : Data.m68 * Data.gen0 = (4 : ZMod 7) • Data.m104 := by
  unfold Data.m68 Data.gen0 Data.m104
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_68_1 : Data.m68 * Data.gen1 = (1 : ZMod 7) • Data.m44 := by
  unfold Data.m68 Data.gen1 Data.m44
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_68_2 : Data.m68 * Data.gen2 = (2 : ZMod 7) • Data.m67 := by
  unfold Data.m68 Data.gen2 Data.m67
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_68_3 : Data.m68 * Data.gen3 = (1 : ZMod 7) • Data.m70 := by
  unfold Data.m68 Data.gen3 Data.m70
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_69_0 : Data.m69 * Data.gen0 = (4 : ZMod 7) • Data.m105 := by
  unfold Data.m69 Data.gen0 Data.m105
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_69_1 : Data.m69 * Data.gen1 = (1 : ZMod 7) • Data.m45 := by
  unfold Data.m69 Data.gen1 Data.m45
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_69_2 : Data.m69 * Data.gen2 = (4 : ZMod 7) • Data.m65 := by
  unfold Data.m69 Data.gen2 Data.m65
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_69_3 : Data.m69 * Data.gen3 = (1 : ZMod 7) • Data.m71 := by
  unfold Data.m69 Data.gen3 Data.m71
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_70_0 : Data.m70 * Data.gen0 = (4 : ZMod 7) • Data.m106 := by
  unfold Data.m70 Data.gen0 Data.m106
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_70_1 : Data.m70 * Data.gen1 = (1 : ZMod 7) • Data.m46 := by
  unfold Data.m70 Data.gen1 Data.m46
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_70_2 : Data.m70 * Data.gen2 = (2 : ZMod 7) • Data.m71 := by
  unfold Data.m70 Data.gen2 Data.m71
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_70_3 : Data.m70 * Data.gen3 = (1 : ZMod 7) • Data.m64 := by
  unfold Data.m70 Data.gen3 Data.m64
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_71_0 : Data.m71 * Data.gen0 = (4 : ZMod 7) • Data.m107 := by
  unfold Data.m71 Data.gen0 Data.m107
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_71_1 : Data.m71 * Data.gen1 = (1 : ZMod 7) • Data.m47 := by
  unfold Data.m71 Data.gen1 Data.m47
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_71_2 : Data.m71 * Data.gen2 = (2 : ZMod 7) • Data.m70 := by
  unfold Data.m71 Data.gen2 Data.m70
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_71_3 : Data.m71 * Data.gen3 = (4 : ZMod 7) • Data.m66 := by
  unfold Data.m71 Data.gen3 Data.m66
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
public theorem transitions_1_2 (k : Fin 12) (i : Fin 4) :
    Data.table ((1, 2), k) * Data.generatorMatrix i =
      Data.scalar ((1, 2), k) i • Data.table (next ((1, 2), k) i) := by
  fin_cases k <;> fin_cases i
  · exact product_60_0
  · exact product_60_1
  · exact product_60_2
  · exact product_60_3
  · exact product_61_0
  · exact product_61_1
  · exact product_61_2
  · exact product_61_3
  · exact product_62_0
  · exact product_62_1
  · exact product_62_2
  · exact product_62_3
  · exact product_63_0
  · exact product_63_1
  · exact product_63_2
  · exact product_63_3
  · exact product_64_0
  · exact product_64_1
  · exact product_64_2
  · exact product_64_3
  · exact product_65_0
  · exact product_65_1
  · exact product_65_2
  · exact product_65_3
  · exact product_66_0
  · exact product_66_1
  · exact product_66_2
  · exact product_66_3
  · exact product_67_0
  · exact product_67_1
  · exact product_67_2
  · exact product_67_3
  · exact product_68_0
  · exact product_68_1
  · exact product_68_2
  · exact product_68_3
  · exact product_69_0
  · exact product_69_1
  · exact product_69_2
  · exact product_69_3
  · exact product_70_0
  · exact product_70_1
  · exact product_70_2
  · exact product_70_3
  · exact product_71_0
  · exact product_71_1
  · exact product_71_2
  · exact product_71_3

end ONan.E9A4.MatrixTable

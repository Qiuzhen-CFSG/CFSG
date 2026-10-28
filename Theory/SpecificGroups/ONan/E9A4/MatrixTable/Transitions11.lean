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
private theorem product_48_0 : Data.m48 * Data.gen0 = (2 : ZMod 7) • Data.m84 := by
  unfold Data.m48 Data.gen0 Data.m84
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_48_1 : Data.m48 * Data.gen1 = (1 : ZMod 7) • Data.m60 := by
  unfold Data.m48 Data.gen1 Data.m60
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_48_2 : Data.m48 * Data.gen2 = (1 : ZMod 7) • Data.m49 := by
  unfold Data.m48 Data.gen2 Data.m49
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_48_3 : Data.m48 * Data.gen3 = (1 : ZMod 7) • Data.m50 := by
  unfold Data.m48 Data.gen3 Data.m50
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_49_0 : Data.m49 * Data.gen0 = (2 : ZMod 7) • Data.m85 := by
  unfold Data.m49 Data.gen0 Data.m85
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_49_1 : Data.m49 * Data.gen1 = (1 : ZMod 7) • Data.m61 := by
  unfold Data.m49 Data.gen1 Data.m61
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_49_2 : Data.m49 * Data.gen2 = (4 : ZMod 7) • Data.m48 := by
  unfold Data.m49 Data.gen2 Data.m48
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_49_3 : Data.m49 * Data.gen3 = (1 : ZMod 7) • Data.m51 := by
  unfold Data.m49 Data.gen3 Data.m51
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_50_0 : Data.m50 * Data.gen0 = (2 : ZMod 7) • Data.m86 := by
  unfold Data.m50 Data.gen0 Data.m86
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_50_1 : Data.m50 * Data.gen1 = (1 : ZMod 7) • Data.m62 := by
  unfold Data.m50 Data.gen1 Data.m62
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_50_2 : Data.m50 * Data.gen2 = (1 : ZMod 7) • Data.m52 := by
  unfold Data.m50 Data.gen2 Data.m52
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_50_3 : Data.m50 * Data.gen3 = (1 : ZMod 7) • Data.m53 := by
  unfold Data.m50 Data.gen3 Data.m53
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_51_0 : Data.m51 * Data.gen0 = (2 : ZMod 7) • Data.m87 := by
  unfold Data.m51 Data.gen0 Data.m87
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_51_1 : Data.m51 * Data.gen1 = (1 : ZMod 7) • Data.m63 := by
  unfold Data.m51 Data.gen1 Data.m63
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_51_2 : Data.m51 * Data.gen2 = (1 : ZMod 7) • Data.m54 := by
  unfold Data.m51 Data.gen2 Data.m54
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_51_3 : Data.m51 * Data.gen3 = (1 : ZMod 7) • Data.m55 := by
  unfold Data.m51 Data.gen3 Data.m55
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_52_0 : Data.m52 * Data.gen0 = (2 : ZMod 7) • Data.m88 := by
  unfold Data.m52 Data.gen0 Data.m88
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_52_1 : Data.m52 * Data.gen1 = (1 : ZMod 7) • Data.m64 := by
  unfold Data.m52 Data.gen1 Data.m64
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_52_2 : Data.m52 * Data.gen2 = (4 : ZMod 7) • Data.m50 := by
  unfold Data.m52 Data.gen2 Data.m50
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_52_3 : Data.m52 * Data.gen3 = (1 : ZMod 7) • Data.m56 := by
  unfold Data.m52 Data.gen3 Data.m56
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_53_0 : Data.m53 * Data.gen0 = (2 : ZMod 7) • Data.m89 := by
  unfold Data.m53 Data.gen0 Data.m89
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_53_1 : Data.m53 * Data.gen1 = (1 : ZMod 7) • Data.m65 := by
  unfold Data.m53 Data.gen1 Data.m65
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_53_2 : Data.m53 * Data.gen2 = (1 : ZMod 7) • Data.m57 := by
  unfold Data.m53 Data.gen2 Data.m57
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_53_3 : Data.m53 * Data.gen3 = (1 : ZMod 7) • Data.m48 := by
  unfold Data.m53 Data.gen3 Data.m48
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_54_0 : Data.m54 * Data.gen0 = (2 : ZMod 7) • Data.m90 := by
  unfold Data.m54 Data.gen0 Data.m90
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_54_1 : Data.m54 * Data.gen1 = (1 : ZMod 7) • Data.m66 := by
  unfold Data.m54 Data.gen1 Data.m66
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_54_2 : Data.m54 * Data.gen2 = (4 : ZMod 7) • Data.m51 := by
  unfold Data.m54 Data.gen2 Data.m51
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_54_3 : Data.m54 * Data.gen3 = (2 : ZMod 7) • Data.m57 := by
  unfold Data.m54 Data.gen3 Data.m57
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_55_0 : Data.m55 * Data.gen0 = (2 : ZMod 7) • Data.m91 := by
  unfold Data.m55 Data.gen0 Data.m91
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_55_1 : Data.m55 * Data.gen1 = (1 : ZMod 7) • Data.m67 := by
  unfold Data.m55 Data.gen1 Data.m67
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_55_2 : Data.m55 * Data.gen2 = (2 : ZMod 7) • Data.m56 := by
  unfold Data.m55 Data.gen2 Data.m56
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_55_3 : Data.m55 * Data.gen3 = (1 : ZMod 7) • Data.m49 := by
  unfold Data.m55 Data.gen3 Data.m49
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_56_0 : Data.m56 * Data.gen0 = (2 : ZMod 7) • Data.m92 := by
  unfold Data.m56 Data.gen0 Data.m92
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_56_1 : Data.m56 * Data.gen1 = (1 : ZMod 7) • Data.m68 := by
  unfold Data.m56 Data.gen1 Data.m68
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_56_2 : Data.m56 * Data.gen2 = (2 : ZMod 7) • Data.m55 := by
  unfold Data.m56 Data.gen2 Data.m55
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_56_3 : Data.m56 * Data.gen3 = (1 : ZMod 7) • Data.m58 := by
  unfold Data.m56 Data.gen3 Data.m58
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_57_0 : Data.m57 * Data.gen0 = (2 : ZMod 7) • Data.m93 := by
  unfold Data.m57 Data.gen0 Data.m93
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_57_1 : Data.m57 * Data.gen1 = (1 : ZMod 7) • Data.m69 := by
  unfold Data.m57 Data.gen1 Data.m69
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_57_2 : Data.m57 * Data.gen2 = (4 : ZMod 7) • Data.m53 := by
  unfold Data.m57 Data.gen2 Data.m53
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_57_3 : Data.m57 * Data.gen3 = (1 : ZMod 7) • Data.m59 := by
  unfold Data.m57 Data.gen3 Data.m59
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_58_0 : Data.m58 * Data.gen0 = (2 : ZMod 7) • Data.m94 := by
  unfold Data.m58 Data.gen0 Data.m94
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_58_1 : Data.m58 * Data.gen1 = (1 : ZMod 7) • Data.m70 := by
  unfold Data.m58 Data.gen1 Data.m70
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_58_2 : Data.m58 * Data.gen2 = (2 : ZMod 7) • Data.m59 := by
  unfold Data.m58 Data.gen2 Data.m59
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_58_3 : Data.m58 * Data.gen3 = (1 : ZMod 7) • Data.m52 := by
  unfold Data.m58 Data.gen3 Data.m52
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_59_0 : Data.m59 * Data.gen0 = (2 : ZMod 7) • Data.m95 := by
  unfold Data.m59 Data.gen0 Data.m95
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_59_1 : Data.m59 * Data.gen1 = (1 : ZMod 7) • Data.m71 := by
  unfold Data.m59 Data.gen1 Data.m71
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_59_2 : Data.m59 * Data.gen2 = (2 : ZMod 7) • Data.m58 := by
  unfold Data.m59 Data.gen2 Data.m58
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_59_3 : Data.m59 * Data.gen3 = (4 : ZMod 7) • Data.m54 := by
  unfold Data.m59 Data.gen3 Data.m54
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
public theorem transitions_1_1 (k : Fin 12) (i : Fin 4) :
    Data.table ((1, 1), k) * Data.generatorMatrix i =
      Data.scalar ((1, 1), k) i • Data.table (next ((1, 1), k) i) := by
  fin_cases k <;> fin_cases i
  · exact product_48_0
  · exact product_48_1
  · exact product_48_2
  · exact product_48_3
  · exact product_49_0
  · exact product_49_1
  · exact product_49_2
  · exact product_49_3
  · exact product_50_0
  · exact product_50_1
  · exact product_50_2
  · exact product_50_3
  · exact product_51_0
  · exact product_51_1
  · exact product_51_2
  · exact product_51_3
  · exact product_52_0
  · exact product_52_1
  · exact product_52_2
  · exact product_52_3
  · exact product_53_0
  · exact product_53_1
  · exact product_53_2
  · exact product_53_3
  · exact product_54_0
  · exact product_54_1
  · exact product_54_2
  · exact product_54_3
  · exact product_55_0
  · exact product_55_1
  · exact product_55_2
  · exact product_55_3
  · exact product_56_0
  · exact product_56_1
  · exact product_56_2
  · exact product_56_3
  · exact product_57_0
  · exact product_57_1
  · exact product_57_2
  · exact product_57_3
  · exact product_58_0
  · exact product_58_1
  · exact product_58_2
  · exact product_58_3
  · exact product_59_0
  · exact product_59_1
  · exact product_59_2
  · exact product_59_3

end ONan.E9A4.MatrixTable

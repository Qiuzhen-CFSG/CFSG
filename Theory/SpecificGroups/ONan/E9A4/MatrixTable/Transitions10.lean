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
private theorem product_36_0 : Data.m36 * Data.gen0 = (1 : ZMod 7) • Data.m72 := by
  unfold Data.m36 Data.gen0 Data.m72
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_36_1 : Data.m36 * Data.gen1 = (1 : ZMod 7) • Data.m48 := by
  unfold Data.m36 Data.gen1 Data.m48
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_36_2 : Data.m36 * Data.gen2 = (1 : ZMod 7) • Data.m37 := by
  unfold Data.m36 Data.gen2 Data.m37
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_36_3 : Data.m36 * Data.gen3 = (1 : ZMod 7) • Data.m38 := by
  unfold Data.m36 Data.gen3 Data.m38
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_37_0 : Data.m37 * Data.gen0 = (1 : ZMod 7) • Data.m73 := by
  unfold Data.m37 Data.gen0 Data.m73
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_37_1 : Data.m37 * Data.gen1 = (1 : ZMod 7) • Data.m49 := by
  unfold Data.m37 Data.gen1 Data.m49
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_37_2 : Data.m37 * Data.gen2 = (4 : ZMod 7) • Data.m36 := by
  unfold Data.m37 Data.gen2 Data.m36
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_37_3 : Data.m37 * Data.gen3 = (1 : ZMod 7) • Data.m39 := by
  unfold Data.m37 Data.gen3 Data.m39
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_38_0 : Data.m38 * Data.gen0 = (1 : ZMod 7) • Data.m74 := by
  unfold Data.m38 Data.gen0 Data.m74
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_38_1 : Data.m38 * Data.gen1 = (1 : ZMod 7) • Data.m50 := by
  unfold Data.m38 Data.gen1 Data.m50
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_38_2 : Data.m38 * Data.gen2 = (1 : ZMod 7) • Data.m40 := by
  unfold Data.m38 Data.gen2 Data.m40
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_38_3 : Data.m38 * Data.gen3 = (1 : ZMod 7) • Data.m41 := by
  unfold Data.m38 Data.gen3 Data.m41
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_39_0 : Data.m39 * Data.gen0 = (1 : ZMod 7) • Data.m75 := by
  unfold Data.m39 Data.gen0 Data.m75
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_39_1 : Data.m39 * Data.gen1 = (1 : ZMod 7) • Data.m51 := by
  unfold Data.m39 Data.gen1 Data.m51
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_39_2 : Data.m39 * Data.gen2 = (1 : ZMod 7) • Data.m42 := by
  unfold Data.m39 Data.gen2 Data.m42
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_39_3 : Data.m39 * Data.gen3 = (1 : ZMod 7) • Data.m43 := by
  unfold Data.m39 Data.gen3 Data.m43
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_40_0 : Data.m40 * Data.gen0 = (1 : ZMod 7) • Data.m76 := by
  unfold Data.m40 Data.gen0 Data.m76
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_40_1 : Data.m40 * Data.gen1 = (1 : ZMod 7) • Data.m52 := by
  unfold Data.m40 Data.gen1 Data.m52
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_40_2 : Data.m40 * Data.gen2 = (4 : ZMod 7) • Data.m38 := by
  unfold Data.m40 Data.gen2 Data.m38
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_40_3 : Data.m40 * Data.gen3 = (1 : ZMod 7) • Data.m44 := by
  unfold Data.m40 Data.gen3 Data.m44
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_41_0 : Data.m41 * Data.gen0 = (1 : ZMod 7) • Data.m77 := by
  unfold Data.m41 Data.gen0 Data.m77
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_41_1 : Data.m41 * Data.gen1 = (1 : ZMod 7) • Data.m53 := by
  unfold Data.m41 Data.gen1 Data.m53
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_41_2 : Data.m41 * Data.gen2 = (1 : ZMod 7) • Data.m45 := by
  unfold Data.m41 Data.gen2 Data.m45
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_41_3 : Data.m41 * Data.gen3 = (1 : ZMod 7) • Data.m36 := by
  unfold Data.m41 Data.gen3 Data.m36
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_42_0 : Data.m42 * Data.gen0 = (1 : ZMod 7) • Data.m78 := by
  unfold Data.m42 Data.gen0 Data.m78
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_42_1 : Data.m42 * Data.gen1 = (1 : ZMod 7) • Data.m54 := by
  unfold Data.m42 Data.gen1 Data.m54
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_42_2 : Data.m42 * Data.gen2 = (4 : ZMod 7) • Data.m39 := by
  unfold Data.m42 Data.gen2 Data.m39
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_42_3 : Data.m42 * Data.gen3 = (2 : ZMod 7) • Data.m45 := by
  unfold Data.m42 Data.gen3 Data.m45
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_43_0 : Data.m43 * Data.gen0 = (1 : ZMod 7) • Data.m79 := by
  unfold Data.m43 Data.gen0 Data.m79
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_43_1 : Data.m43 * Data.gen1 = (1 : ZMod 7) • Data.m55 := by
  unfold Data.m43 Data.gen1 Data.m55
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_43_2 : Data.m43 * Data.gen2 = (2 : ZMod 7) • Data.m44 := by
  unfold Data.m43 Data.gen2 Data.m44
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_43_3 : Data.m43 * Data.gen3 = (1 : ZMod 7) • Data.m37 := by
  unfold Data.m43 Data.gen3 Data.m37
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_44_0 : Data.m44 * Data.gen0 = (1 : ZMod 7) • Data.m80 := by
  unfold Data.m44 Data.gen0 Data.m80
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_44_1 : Data.m44 * Data.gen1 = (1 : ZMod 7) • Data.m56 := by
  unfold Data.m44 Data.gen1 Data.m56
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_44_2 : Data.m44 * Data.gen2 = (2 : ZMod 7) • Data.m43 := by
  unfold Data.m44 Data.gen2 Data.m43
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_44_3 : Data.m44 * Data.gen3 = (1 : ZMod 7) • Data.m46 := by
  unfold Data.m44 Data.gen3 Data.m46
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_45_0 : Data.m45 * Data.gen0 = (1 : ZMod 7) • Data.m81 := by
  unfold Data.m45 Data.gen0 Data.m81
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_45_1 : Data.m45 * Data.gen1 = (1 : ZMod 7) • Data.m57 := by
  unfold Data.m45 Data.gen1 Data.m57
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_45_2 : Data.m45 * Data.gen2 = (4 : ZMod 7) • Data.m41 := by
  unfold Data.m45 Data.gen2 Data.m41
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_45_3 : Data.m45 * Data.gen3 = (1 : ZMod 7) • Data.m47 := by
  unfold Data.m45 Data.gen3 Data.m47
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_46_0 : Data.m46 * Data.gen0 = (1 : ZMod 7) • Data.m82 := by
  unfold Data.m46 Data.gen0 Data.m82
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_46_1 : Data.m46 * Data.gen1 = (1 : ZMod 7) • Data.m58 := by
  unfold Data.m46 Data.gen1 Data.m58
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_46_2 : Data.m46 * Data.gen2 = (2 : ZMod 7) • Data.m47 := by
  unfold Data.m46 Data.gen2 Data.m47
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_46_3 : Data.m46 * Data.gen3 = (1 : ZMod 7) • Data.m40 := by
  unfold Data.m46 Data.gen3 Data.m40
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_47_0 : Data.m47 * Data.gen0 = (1 : ZMod 7) • Data.m83 := by
  unfold Data.m47 Data.gen0 Data.m83
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_47_1 : Data.m47 * Data.gen1 = (1 : ZMod 7) • Data.m59 := by
  unfold Data.m47 Data.gen1 Data.m59
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_47_2 : Data.m47 * Data.gen2 = (2 : ZMod 7) • Data.m46 := by
  unfold Data.m47 Data.gen2 Data.m46
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_47_3 : Data.m47 * Data.gen3 = (4 : ZMod 7) • Data.m42 := by
  unfold Data.m47 Data.gen3 Data.m42
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
public theorem transitions_1_0 (k : Fin 12) (i : Fin 4) :
    Data.table ((1, 0), k) * Data.generatorMatrix i =
      Data.scalar ((1, 0), k) i • Data.table (next ((1, 0), k) i) := by
  fin_cases k <;> fin_cases i
  · exact product_36_0
  · exact product_36_1
  · exact product_36_2
  · exact product_36_3
  · exact product_37_0
  · exact product_37_1
  · exact product_37_2
  · exact product_37_3
  · exact product_38_0
  · exact product_38_1
  · exact product_38_2
  · exact product_38_3
  · exact product_39_0
  · exact product_39_1
  · exact product_39_2
  · exact product_39_3
  · exact product_40_0
  · exact product_40_1
  · exact product_40_2
  · exact product_40_3
  · exact product_41_0
  · exact product_41_1
  · exact product_41_2
  · exact product_41_3
  · exact product_42_0
  · exact product_42_1
  · exact product_42_2
  · exact product_42_3
  · exact product_43_0
  · exact product_43_1
  · exact product_43_2
  · exact product_43_3
  · exact product_44_0
  · exact product_44_1
  · exact product_44_2
  · exact product_44_3
  · exact product_45_0
  · exact product_45_1
  · exact product_45_2
  · exact product_45_3
  · exact product_46_0
  · exact product_46_1
  · exact product_46_2
  · exact product_46_3
  · exact product_47_0
  · exact product_47_1
  · exact product_47_2
  · exact product_47_3

end ONan.E9A4.MatrixTable

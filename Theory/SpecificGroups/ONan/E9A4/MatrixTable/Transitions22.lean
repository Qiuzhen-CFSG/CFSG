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
private theorem product_96_0 : Data.m96 * Data.gen0 = (4 : ZMod 7) • Data.m24 := by
  unfold Data.m96 Data.gen0 Data.m24
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_96_1 : Data.m96 * Data.gen1 = (1 : ZMod 7) • Data.m72 := by
  unfold Data.m96 Data.gen1 Data.m72
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_96_2 : Data.m96 * Data.gen2 = (1 : ZMod 7) • Data.m97 := by
  unfold Data.m96 Data.gen2 Data.m97
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_96_3 : Data.m96 * Data.gen3 = (1 : ZMod 7) • Data.m98 := by
  unfold Data.m96 Data.gen3 Data.m98
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_97_0 : Data.m97 * Data.gen0 = (4 : ZMod 7) • Data.m25 := by
  unfold Data.m97 Data.gen0 Data.m25
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_97_1 : Data.m97 * Data.gen1 = (1 : ZMod 7) • Data.m73 := by
  unfold Data.m97 Data.gen1 Data.m73
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_97_2 : Data.m97 * Data.gen2 = (4 : ZMod 7) • Data.m96 := by
  unfold Data.m97 Data.gen2 Data.m96
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_97_3 : Data.m97 * Data.gen3 = (1 : ZMod 7) • Data.m99 := by
  unfold Data.m97 Data.gen3 Data.m99
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_98_0 : Data.m98 * Data.gen0 = (4 : ZMod 7) • Data.m26 := by
  unfold Data.m98 Data.gen0 Data.m26
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_98_1 : Data.m98 * Data.gen1 = (1 : ZMod 7) • Data.m74 := by
  unfold Data.m98 Data.gen1 Data.m74
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_98_2 : Data.m98 * Data.gen2 = (1 : ZMod 7) • Data.m100 := by
  unfold Data.m98 Data.gen2 Data.m100
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_98_3 : Data.m98 * Data.gen3 = (1 : ZMod 7) • Data.m101 := by
  unfold Data.m98 Data.gen3 Data.m101
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_99_0 : Data.m99 * Data.gen0 = (4 : ZMod 7) • Data.m27 := by
  unfold Data.m99 Data.gen0 Data.m27
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_99_1 : Data.m99 * Data.gen1 = (1 : ZMod 7) • Data.m75 := by
  unfold Data.m99 Data.gen1 Data.m75
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_99_2 : Data.m99 * Data.gen2 = (1 : ZMod 7) • Data.m102 := by
  unfold Data.m99 Data.gen2 Data.m102
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_99_3 : Data.m99 * Data.gen3 = (1 : ZMod 7) • Data.m103 := by
  unfold Data.m99 Data.gen3 Data.m103
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_100_0 : Data.m100 * Data.gen0 = (4 : ZMod 7) • Data.m28 := by
  unfold Data.m100 Data.gen0 Data.m28
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_100_1 : Data.m100 * Data.gen1 = (1 : ZMod 7) • Data.m76 := by
  unfold Data.m100 Data.gen1 Data.m76
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_100_2 : Data.m100 * Data.gen2 = (4 : ZMod 7) • Data.m98 := by
  unfold Data.m100 Data.gen2 Data.m98
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_100_3 : Data.m100 * Data.gen3 = (1 : ZMod 7) • Data.m104 := by
  unfold Data.m100 Data.gen3 Data.m104
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_101_0 : Data.m101 * Data.gen0 = (4 : ZMod 7) • Data.m29 := by
  unfold Data.m101 Data.gen0 Data.m29
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_101_1 : Data.m101 * Data.gen1 = (1 : ZMod 7) • Data.m77 := by
  unfold Data.m101 Data.gen1 Data.m77
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_101_2 : Data.m101 * Data.gen2 = (1 : ZMod 7) • Data.m105 := by
  unfold Data.m101 Data.gen2 Data.m105
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_101_3 : Data.m101 * Data.gen3 = (1 : ZMod 7) • Data.m96 := by
  unfold Data.m101 Data.gen3 Data.m96
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_102_0 : Data.m102 * Data.gen0 = (4 : ZMod 7) • Data.m30 := by
  unfold Data.m102 Data.gen0 Data.m30
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_102_1 : Data.m102 * Data.gen1 = (1 : ZMod 7) • Data.m78 := by
  unfold Data.m102 Data.gen1 Data.m78
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_102_2 : Data.m102 * Data.gen2 = (4 : ZMod 7) • Data.m99 := by
  unfold Data.m102 Data.gen2 Data.m99
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_102_3 : Data.m102 * Data.gen3 = (2 : ZMod 7) • Data.m105 := by
  unfold Data.m102 Data.gen3 Data.m105
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_103_0 : Data.m103 * Data.gen0 = (4 : ZMod 7) • Data.m31 := by
  unfold Data.m103 Data.gen0 Data.m31
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_103_1 : Data.m103 * Data.gen1 = (1 : ZMod 7) • Data.m79 := by
  unfold Data.m103 Data.gen1 Data.m79
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_103_2 : Data.m103 * Data.gen2 = (2 : ZMod 7) • Data.m104 := by
  unfold Data.m103 Data.gen2 Data.m104
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_103_3 : Data.m103 * Data.gen3 = (1 : ZMod 7) • Data.m97 := by
  unfold Data.m103 Data.gen3 Data.m97
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_104_0 : Data.m104 * Data.gen0 = (4 : ZMod 7) • Data.m32 := by
  unfold Data.m104 Data.gen0 Data.m32
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_104_1 : Data.m104 * Data.gen1 = (1 : ZMod 7) • Data.m80 := by
  unfold Data.m104 Data.gen1 Data.m80
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_104_2 : Data.m104 * Data.gen2 = (2 : ZMod 7) • Data.m103 := by
  unfold Data.m104 Data.gen2 Data.m103
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_104_3 : Data.m104 * Data.gen3 = (1 : ZMod 7) • Data.m106 := by
  unfold Data.m104 Data.gen3 Data.m106
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_105_0 : Data.m105 * Data.gen0 = (4 : ZMod 7) • Data.m33 := by
  unfold Data.m105 Data.gen0 Data.m33
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_105_1 : Data.m105 * Data.gen1 = (1 : ZMod 7) • Data.m81 := by
  unfold Data.m105 Data.gen1 Data.m81
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_105_2 : Data.m105 * Data.gen2 = (4 : ZMod 7) • Data.m101 := by
  unfold Data.m105 Data.gen2 Data.m101
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_105_3 : Data.m105 * Data.gen3 = (1 : ZMod 7) • Data.m107 := by
  unfold Data.m105 Data.gen3 Data.m107
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_106_0 : Data.m106 * Data.gen0 = (4 : ZMod 7) • Data.m34 := by
  unfold Data.m106 Data.gen0 Data.m34
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_106_1 : Data.m106 * Data.gen1 = (1 : ZMod 7) • Data.m82 := by
  unfold Data.m106 Data.gen1 Data.m82
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_106_2 : Data.m106 * Data.gen2 = (2 : ZMod 7) • Data.m107 := by
  unfold Data.m106 Data.gen2 Data.m107
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_106_3 : Data.m106 * Data.gen3 = (1 : ZMod 7) • Data.m100 := by
  unfold Data.m106 Data.gen3 Data.m100
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_107_0 : Data.m107 * Data.gen0 = (4 : ZMod 7) • Data.m35 := by
  unfold Data.m107 Data.gen0 Data.m35
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_107_1 : Data.m107 * Data.gen1 = (1 : ZMod 7) • Data.m83 := by
  unfold Data.m107 Data.gen1 Data.m83
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_107_2 : Data.m107 * Data.gen2 = (2 : ZMod 7) • Data.m106 := by
  unfold Data.m107 Data.gen2 Data.m106
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_107_3 : Data.m107 * Data.gen3 = (4 : ZMod 7) • Data.m102 := by
  unfold Data.m107 Data.gen3 Data.m102
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
public theorem transitions_2_2 (k : Fin 12) (i : Fin 4) :
    Data.table ((2, 2), k) * Data.generatorMatrix i =
      Data.scalar ((2, 2), k) i • Data.table (next ((2, 2), k) i) := by
  fin_cases k <;> fin_cases i
  · exact product_96_0
  · exact product_96_1
  · exact product_96_2
  · exact product_96_3
  · exact product_97_0
  · exact product_97_1
  · exact product_97_2
  · exact product_97_3
  · exact product_98_0
  · exact product_98_1
  · exact product_98_2
  · exact product_98_3
  · exact product_99_0
  · exact product_99_1
  · exact product_99_2
  · exact product_99_3
  · exact product_100_0
  · exact product_100_1
  · exact product_100_2
  · exact product_100_3
  · exact product_101_0
  · exact product_101_1
  · exact product_101_2
  · exact product_101_3
  · exact product_102_0
  · exact product_102_1
  · exact product_102_2
  · exact product_102_3
  · exact product_103_0
  · exact product_103_1
  · exact product_103_2
  · exact product_103_3
  · exact product_104_0
  · exact product_104_1
  · exact product_104_2
  · exact product_104_3
  · exact product_105_0
  · exact product_105_1
  · exact product_105_2
  · exact product_105_3
  · exact product_106_0
  · exact product_106_1
  · exact product_106_2
  · exact product_106_3
  · exact product_107_0
  · exact product_107_1
  · exact product_107_2
  · exact product_107_3

end ONan.E9A4.MatrixTable

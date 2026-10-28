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
private theorem product_12_0 : Data.m12 * Data.gen0 = (2 : ZMod 7) • Data.m48 := by
  unfold Data.m12 Data.gen0 Data.m48
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_12_1 : Data.m12 * Data.gen1 = (1 : ZMod 7) • Data.m24 := by
  unfold Data.m12 Data.gen1 Data.m24
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_12_2 : Data.m12 * Data.gen2 = (1 : ZMod 7) • Data.m13 := by
  unfold Data.m12 Data.gen2 Data.m13
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_12_3 : Data.m12 * Data.gen3 = (1 : ZMod 7) • Data.m14 := by
  unfold Data.m12 Data.gen3 Data.m14
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_13_0 : Data.m13 * Data.gen0 = (2 : ZMod 7) • Data.m49 := by
  unfold Data.m13 Data.gen0 Data.m49
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_13_1 : Data.m13 * Data.gen1 = (1 : ZMod 7) • Data.m25 := by
  unfold Data.m13 Data.gen1 Data.m25
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_13_2 : Data.m13 * Data.gen2 = (4 : ZMod 7) • Data.m12 := by
  unfold Data.m13 Data.gen2 Data.m12
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_13_3 : Data.m13 * Data.gen3 = (1 : ZMod 7) • Data.m15 := by
  unfold Data.m13 Data.gen3 Data.m15
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_14_0 : Data.m14 * Data.gen0 = (2 : ZMod 7) • Data.m50 := by
  unfold Data.m14 Data.gen0 Data.m50
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_14_1 : Data.m14 * Data.gen1 = (1 : ZMod 7) • Data.m26 := by
  unfold Data.m14 Data.gen1 Data.m26
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_14_2 : Data.m14 * Data.gen2 = (1 : ZMod 7) • Data.m16 := by
  unfold Data.m14 Data.gen2 Data.m16
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_14_3 : Data.m14 * Data.gen3 = (1 : ZMod 7) • Data.m17 := by
  unfold Data.m14 Data.gen3 Data.m17
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_15_0 : Data.m15 * Data.gen0 = (2 : ZMod 7) • Data.m51 := by
  unfold Data.m15 Data.gen0 Data.m51
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_15_1 : Data.m15 * Data.gen1 = (1 : ZMod 7) • Data.m27 := by
  unfold Data.m15 Data.gen1 Data.m27
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_15_2 : Data.m15 * Data.gen2 = (1 : ZMod 7) • Data.m18 := by
  unfold Data.m15 Data.gen2 Data.m18
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_15_3 : Data.m15 * Data.gen3 = (1 : ZMod 7) • Data.m19 := by
  unfold Data.m15 Data.gen3 Data.m19
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_16_0 : Data.m16 * Data.gen0 = (2 : ZMod 7) • Data.m52 := by
  unfold Data.m16 Data.gen0 Data.m52
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_16_1 : Data.m16 * Data.gen1 = (1 : ZMod 7) • Data.m28 := by
  unfold Data.m16 Data.gen1 Data.m28
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_16_2 : Data.m16 * Data.gen2 = (4 : ZMod 7) • Data.m14 := by
  unfold Data.m16 Data.gen2 Data.m14
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_16_3 : Data.m16 * Data.gen3 = (1 : ZMod 7) • Data.m20 := by
  unfold Data.m16 Data.gen3 Data.m20
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_17_0 : Data.m17 * Data.gen0 = (2 : ZMod 7) • Data.m53 := by
  unfold Data.m17 Data.gen0 Data.m53
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_17_1 : Data.m17 * Data.gen1 = (1 : ZMod 7) • Data.m29 := by
  unfold Data.m17 Data.gen1 Data.m29
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_17_2 : Data.m17 * Data.gen2 = (1 : ZMod 7) • Data.m21 := by
  unfold Data.m17 Data.gen2 Data.m21
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_17_3 : Data.m17 * Data.gen3 = (1 : ZMod 7) • Data.m12 := by
  unfold Data.m17 Data.gen3 Data.m12
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_18_0 : Data.m18 * Data.gen0 = (2 : ZMod 7) • Data.m54 := by
  unfold Data.m18 Data.gen0 Data.m54
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_18_1 : Data.m18 * Data.gen1 = (1 : ZMod 7) • Data.m30 := by
  unfold Data.m18 Data.gen1 Data.m30
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_18_2 : Data.m18 * Data.gen2 = (4 : ZMod 7) • Data.m15 := by
  unfold Data.m18 Data.gen2 Data.m15
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_18_3 : Data.m18 * Data.gen3 = (2 : ZMod 7) • Data.m21 := by
  unfold Data.m18 Data.gen3 Data.m21
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_19_0 : Data.m19 * Data.gen0 = (2 : ZMod 7) • Data.m55 := by
  unfold Data.m19 Data.gen0 Data.m55
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_19_1 : Data.m19 * Data.gen1 = (1 : ZMod 7) • Data.m31 := by
  unfold Data.m19 Data.gen1 Data.m31
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_19_2 : Data.m19 * Data.gen2 = (2 : ZMod 7) • Data.m20 := by
  unfold Data.m19 Data.gen2 Data.m20
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_19_3 : Data.m19 * Data.gen3 = (1 : ZMod 7) • Data.m13 := by
  unfold Data.m19 Data.gen3 Data.m13
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_20_0 : Data.m20 * Data.gen0 = (2 : ZMod 7) • Data.m56 := by
  unfold Data.m20 Data.gen0 Data.m56
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_20_1 : Data.m20 * Data.gen1 = (1 : ZMod 7) • Data.m32 := by
  unfold Data.m20 Data.gen1 Data.m32
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_20_2 : Data.m20 * Data.gen2 = (2 : ZMod 7) • Data.m19 := by
  unfold Data.m20 Data.gen2 Data.m19
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_20_3 : Data.m20 * Data.gen3 = (1 : ZMod 7) • Data.m22 := by
  unfold Data.m20 Data.gen3 Data.m22
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_21_0 : Data.m21 * Data.gen0 = (2 : ZMod 7) • Data.m57 := by
  unfold Data.m21 Data.gen0 Data.m57
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_21_1 : Data.m21 * Data.gen1 = (1 : ZMod 7) • Data.m33 := by
  unfold Data.m21 Data.gen1 Data.m33
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_21_2 : Data.m21 * Data.gen2 = (4 : ZMod 7) • Data.m17 := by
  unfold Data.m21 Data.gen2 Data.m17
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_21_3 : Data.m21 * Data.gen3 = (1 : ZMod 7) • Data.m23 := by
  unfold Data.m21 Data.gen3 Data.m23
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_22_0 : Data.m22 * Data.gen0 = (2 : ZMod 7) • Data.m58 := by
  unfold Data.m22 Data.gen0 Data.m58
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_22_1 : Data.m22 * Data.gen1 = (1 : ZMod 7) • Data.m34 := by
  unfold Data.m22 Data.gen1 Data.m34
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_22_2 : Data.m22 * Data.gen2 = (2 : ZMod 7) • Data.m23 := by
  unfold Data.m22 Data.gen2 Data.m23
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_22_3 : Data.m22 * Data.gen3 = (1 : ZMod 7) • Data.m16 := by
  unfold Data.m22 Data.gen3 Data.m16
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_23_0 : Data.m23 * Data.gen0 = (2 : ZMod 7) • Data.m59 := by
  unfold Data.m23 Data.gen0 Data.m59
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_23_1 : Data.m23 * Data.gen1 = (1 : ZMod 7) • Data.m35 := by
  unfold Data.m23 Data.gen1 Data.m35
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_23_2 : Data.m23 * Data.gen2 = (2 : ZMod 7) • Data.m22 := by
  unfold Data.m23 Data.gen2 Data.m22
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_23_3 : Data.m23 * Data.gen3 = (4 : ZMod 7) • Data.m18 := by
  unfold Data.m23 Data.gen3 Data.m18
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

public theorem transitions_0_1 (k : Fin 12) (i : Fin 4) :
    Data.table ((0, 1), k) * Data.generatorMatrix i =
      Data.scalar ((0, 1), k) i • Data.table (next ((0, 1), k) i) := by
  fin_cases k <;> fin_cases i
  · exact product_12_0
  · exact product_12_1
  · exact product_12_2
  · exact product_12_3
  · exact product_13_0
  · exact product_13_1
  · exact product_13_2
  · exact product_13_3
  · exact product_14_0
  · exact product_14_1
  · exact product_14_2
  · exact product_14_3
  · exact product_15_0
  · exact product_15_1
  · exact product_15_2
  · exact product_15_3
  · exact product_16_0
  · exact product_16_1
  · exact product_16_2
  · exact product_16_3
  · exact product_17_0
  · exact product_17_1
  · exact product_17_2
  · exact product_17_3
  · exact product_18_0
  · exact product_18_1
  · exact product_18_2
  · exact product_18_3
  · exact product_19_0
  · exact product_19_1
  · exact product_19_2
  · exact product_19_3
  · exact product_20_0
  · exact product_20_1
  · exact product_20_2
  · exact product_20_3
  · exact product_21_0
  · exact product_21_1
  · exact product_21_2
  · exact product_21_3
  · exact product_22_0
  · exact product_22_1
  · exact product_22_2
  · exact product_22_3
  · exact product_23_0
  · exact product_23_1
  · exact product_23_2
  · exact product_23_3

end ONan.E9A4.MatrixTable

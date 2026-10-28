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
private theorem product_0_0 : Data.m0 * Data.gen0 = (1 : ZMod 7) • Data.m36 := by
  unfold Data.m0 Data.gen0 Data.m36
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_0_1 : Data.m0 * Data.gen1 = (1 : ZMod 7) • Data.m12 := by
  unfold Data.m0 Data.gen1 Data.m12
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_0_2 : Data.m0 * Data.gen2 = (1 : ZMod 7) • Data.m1 := by
  unfold Data.m0 Data.gen2 Data.m1
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_0_3 : Data.m0 * Data.gen3 = (1 : ZMod 7) • Data.m2 := by
  unfold Data.m0 Data.gen3 Data.m2
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_1_0 : Data.m1 * Data.gen0 = (1 : ZMod 7) • Data.m37 := by
  unfold Data.m1 Data.gen0 Data.m37
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_1_1 : Data.m1 * Data.gen1 = (1 : ZMod 7) • Data.m13 := by
  unfold Data.m1 Data.gen1 Data.m13
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_1_2 : Data.m1 * Data.gen2 = (4 : ZMod 7) • Data.m0 := by
  unfold Data.m1 Data.gen2 Data.m0
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_1_3 : Data.m1 * Data.gen3 = (1 : ZMod 7) • Data.m3 := by
  unfold Data.m1 Data.gen3 Data.m3
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_2_0 : Data.m2 * Data.gen0 = (1 : ZMod 7) • Data.m38 := by
  unfold Data.m2 Data.gen0 Data.m38
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_2_1 : Data.m2 * Data.gen1 = (1 : ZMod 7) • Data.m14 := by
  unfold Data.m2 Data.gen1 Data.m14
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_2_2 : Data.m2 * Data.gen2 = (1 : ZMod 7) • Data.m4 := by
  unfold Data.m2 Data.gen2 Data.m4
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_2_3 : Data.m2 * Data.gen3 = (1 : ZMod 7) • Data.m5 := by
  unfold Data.m2 Data.gen3 Data.m5
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_3_0 : Data.m3 * Data.gen0 = (1 : ZMod 7) • Data.m39 := by
  unfold Data.m3 Data.gen0 Data.m39
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_3_1 : Data.m3 * Data.gen1 = (1 : ZMod 7) • Data.m15 := by
  unfold Data.m3 Data.gen1 Data.m15
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_3_2 : Data.m3 * Data.gen2 = (1 : ZMod 7) • Data.m6 := by
  unfold Data.m3 Data.gen2 Data.m6
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_3_3 : Data.m3 * Data.gen3 = (1 : ZMod 7) • Data.m7 := by
  unfold Data.m3 Data.gen3 Data.m7
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_4_0 : Data.m4 * Data.gen0 = (1 : ZMod 7) • Data.m40 := by
  unfold Data.m4 Data.gen0 Data.m40
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_4_1 : Data.m4 * Data.gen1 = (1 : ZMod 7) • Data.m16 := by
  unfold Data.m4 Data.gen1 Data.m16
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_4_2 : Data.m4 * Data.gen2 = (4 : ZMod 7) • Data.m2 := by
  unfold Data.m4 Data.gen2 Data.m2
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_4_3 : Data.m4 * Data.gen3 = (1 : ZMod 7) • Data.m8 := by
  unfold Data.m4 Data.gen3 Data.m8
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_5_0 : Data.m5 * Data.gen0 = (1 : ZMod 7) • Data.m41 := by
  unfold Data.m5 Data.gen0 Data.m41
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_5_1 : Data.m5 * Data.gen1 = (1 : ZMod 7) • Data.m17 := by
  unfold Data.m5 Data.gen1 Data.m17
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_5_2 : Data.m5 * Data.gen2 = (1 : ZMod 7) • Data.m9 := by
  unfold Data.m5 Data.gen2 Data.m9
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_5_3 : Data.m5 * Data.gen3 = (1 : ZMod 7) • Data.m0 := by
  unfold Data.m5 Data.gen3 Data.m0
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_6_0 : Data.m6 * Data.gen0 = (1 : ZMod 7) • Data.m42 := by
  unfold Data.m6 Data.gen0 Data.m42
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_6_1 : Data.m6 * Data.gen1 = (1 : ZMod 7) • Data.m18 := by
  unfold Data.m6 Data.gen1 Data.m18
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_6_2 : Data.m6 * Data.gen2 = (4 : ZMod 7) • Data.m3 := by
  unfold Data.m6 Data.gen2 Data.m3
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_6_3 : Data.m6 * Data.gen3 = (2 : ZMod 7) • Data.m9 := by
  unfold Data.m6 Data.gen3 Data.m9
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_7_0 : Data.m7 * Data.gen0 = (1 : ZMod 7) • Data.m43 := by
  unfold Data.m7 Data.gen0 Data.m43
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_7_1 : Data.m7 * Data.gen1 = (1 : ZMod 7) • Data.m19 := by
  unfold Data.m7 Data.gen1 Data.m19
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_7_2 : Data.m7 * Data.gen2 = (2 : ZMod 7) • Data.m8 := by
  unfold Data.m7 Data.gen2 Data.m8
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_7_3 : Data.m7 * Data.gen3 = (1 : ZMod 7) • Data.m1 := by
  unfold Data.m7 Data.gen3 Data.m1
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_8_0 : Data.m8 * Data.gen0 = (1 : ZMod 7) • Data.m44 := by
  unfold Data.m8 Data.gen0 Data.m44
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_8_1 : Data.m8 * Data.gen1 = (1 : ZMod 7) • Data.m20 := by
  unfold Data.m8 Data.gen1 Data.m20
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_8_2 : Data.m8 * Data.gen2 = (2 : ZMod 7) • Data.m7 := by
  unfold Data.m8 Data.gen2 Data.m7
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_8_3 : Data.m8 * Data.gen3 = (1 : ZMod 7) • Data.m10 := by
  unfold Data.m8 Data.gen3 Data.m10
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_9_0 : Data.m9 * Data.gen0 = (1 : ZMod 7) • Data.m45 := by
  unfold Data.m9 Data.gen0 Data.m45
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_9_1 : Data.m9 * Data.gen1 = (1 : ZMod 7) • Data.m21 := by
  unfold Data.m9 Data.gen1 Data.m21
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_9_2 : Data.m9 * Data.gen2 = (4 : ZMod 7) • Data.m5 := by
  unfold Data.m9 Data.gen2 Data.m5
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_9_3 : Data.m9 * Data.gen3 = (1 : ZMod 7) • Data.m11 := by
  unfold Data.m9 Data.gen3 Data.m11
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_10_0 : Data.m10 * Data.gen0 = (1 : ZMod 7) • Data.m46 := by
  unfold Data.m10 Data.gen0 Data.m46
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_10_1 : Data.m10 * Data.gen1 = (1 : ZMod 7) • Data.m22 := by
  unfold Data.m10 Data.gen1 Data.m22
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_10_2 : Data.m10 * Data.gen2 = (2 : ZMod 7) • Data.m11 := by
  unfold Data.m10 Data.gen2 Data.m11
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_10_3 : Data.m10 * Data.gen3 = (1 : ZMod 7) • Data.m4 := by
  unfold Data.m10 Data.gen3 Data.m4
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_11_0 : Data.m11 * Data.gen0 = (1 : ZMod 7) • Data.m47 := by
  unfold Data.m11 Data.gen0 Data.m47
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_11_1 : Data.m11 * Data.gen1 = (1 : ZMod 7) • Data.m23 := by
  unfold Data.m11 Data.gen1 Data.m23
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_11_2 : Data.m11 * Data.gen2 = (2 : ZMod 7) • Data.m10 := by
  unfold Data.m11 Data.gen2 Data.m10
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_11_3 : Data.m11 * Data.gen3 = (4 : ZMod 7) • Data.m6 := by
  unfold Data.m11 Data.gen3 Data.m6
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

public theorem transitions_0_0 (k : Fin 12) (i : Fin 4) :
    Data.table ((0, 0), k) * Data.generatorMatrix i =
      Data.scalar ((0, 0), k) i • Data.table (next ((0, 0), k) i) := by
  fin_cases k <;> fin_cases i
  · exact product_0_0
  · exact product_0_1
  · exact product_0_2
  · exact product_0_3
  · exact product_1_0
  · exact product_1_1
  · exact product_1_2
  · exact product_1_3
  · exact product_2_0
  · exact product_2_1
  · exact product_2_2
  · exact product_2_3
  · exact product_3_0
  · exact product_3_1
  · exact product_3_2
  · exact product_3_3
  · exact product_4_0
  · exact product_4_1
  · exact product_4_2
  · exact product_4_3
  · exact product_5_0
  · exact product_5_1
  · exact product_5_2
  · exact product_5_3
  · exact product_6_0
  · exact product_6_1
  · exact product_6_2
  · exact product_6_3
  · exact product_7_0
  · exact product_7_1
  · exact product_7_2
  · exact product_7_3
  · exact product_8_0
  · exact product_8_1
  · exact product_8_2
  · exact product_8_3
  · exact product_9_0
  · exact product_9_1
  · exact product_9_2
  · exact product_9_3
  · exact product_10_0
  · exact product_10_1
  · exact product_10_2
  · exact product_10_3
  · exact product_11_0
  · exact product_11_1
  · exact product_11_2
  · exact product_11_3

end ONan.E9A4.MatrixTable

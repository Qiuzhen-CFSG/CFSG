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
private theorem product_24_0 : Data.m24 * Data.gen0 = (4 : ZMod 7) • Data.m60 := by
  unfold Data.m24 Data.gen0 Data.m60
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_24_1 : Data.m24 * Data.gen1 = (1 : ZMod 7) • Data.m0 := by
  unfold Data.m24 Data.gen1 Data.m0
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_24_2 : Data.m24 * Data.gen2 = (1 : ZMod 7) • Data.m25 := by
  unfold Data.m24 Data.gen2 Data.m25
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_24_3 : Data.m24 * Data.gen3 = (1 : ZMod 7) • Data.m26 := by
  unfold Data.m24 Data.gen3 Data.m26
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_25_0 : Data.m25 * Data.gen0 = (4 : ZMod 7) • Data.m61 := by
  unfold Data.m25 Data.gen0 Data.m61
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_25_1 : Data.m25 * Data.gen1 = (1 : ZMod 7) • Data.m1 := by
  unfold Data.m25 Data.gen1 Data.m1
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_25_2 : Data.m25 * Data.gen2 = (4 : ZMod 7) • Data.m24 := by
  unfold Data.m25 Data.gen2 Data.m24
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_25_3 : Data.m25 * Data.gen3 = (1 : ZMod 7) • Data.m27 := by
  unfold Data.m25 Data.gen3 Data.m27
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_26_0 : Data.m26 * Data.gen0 = (4 : ZMod 7) • Data.m62 := by
  unfold Data.m26 Data.gen0 Data.m62
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_26_1 : Data.m26 * Data.gen1 = (1 : ZMod 7) • Data.m2 := by
  unfold Data.m26 Data.gen1 Data.m2
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_26_2 : Data.m26 * Data.gen2 = (1 : ZMod 7) • Data.m28 := by
  unfold Data.m26 Data.gen2 Data.m28
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_26_3 : Data.m26 * Data.gen3 = (1 : ZMod 7) • Data.m29 := by
  unfold Data.m26 Data.gen3 Data.m29
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_27_0 : Data.m27 * Data.gen0 = (4 : ZMod 7) • Data.m63 := by
  unfold Data.m27 Data.gen0 Data.m63
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_27_1 : Data.m27 * Data.gen1 = (1 : ZMod 7) • Data.m3 := by
  unfold Data.m27 Data.gen1 Data.m3
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_27_2 : Data.m27 * Data.gen2 = (1 : ZMod 7) • Data.m30 := by
  unfold Data.m27 Data.gen2 Data.m30
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_27_3 : Data.m27 * Data.gen3 = (1 : ZMod 7) • Data.m31 := by
  unfold Data.m27 Data.gen3 Data.m31
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_28_0 : Data.m28 * Data.gen0 = (4 : ZMod 7) • Data.m64 := by
  unfold Data.m28 Data.gen0 Data.m64
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_28_1 : Data.m28 * Data.gen1 = (1 : ZMod 7) • Data.m4 := by
  unfold Data.m28 Data.gen1 Data.m4
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_28_2 : Data.m28 * Data.gen2 = (4 : ZMod 7) • Data.m26 := by
  unfold Data.m28 Data.gen2 Data.m26
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_28_3 : Data.m28 * Data.gen3 = (1 : ZMod 7) • Data.m32 := by
  unfold Data.m28 Data.gen3 Data.m32
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_29_0 : Data.m29 * Data.gen0 = (4 : ZMod 7) • Data.m65 := by
  unfold Data.m29 Data.gen0 Data.m65
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_29_1 : Data.m29 * Data.gen1 = (1 : ZMod 7) • Data.m5 := by
  unfold Data.m29 Data.gen1 Data.m5
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_29_2 : Data.m29 * Data.gen2 = (1 : ZMod 7) • Data.m33 := by
  unfold Data.m29 Data.gen2 Data.m33
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_29_3 : Data.m29 * Data.gen3 = (1 : ZMod 7) • Data.m24 := by
  unfold Data.m29 Data.gen3 Data.m24
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_30_0 : Data.m30 * Data.gen0 = (4 : ZMod 7) • Data.m66 := by
  unfold Data.m30 Data.gen0 Data.m66
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_30_1 : Data.m30 * Data.gen1 = (1 : ZMod 7) • Data.m6 := by
  unfold Data.m30 Data.gen1 Data.m6
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_30_2 : Data.m30 * Data.gen2 = (4 : ZMod 7) • Data.m27 := by
  unfold Data.m30 Data.gen2 Data.m27
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_30_3 : Data.m30 * Data.gen3 = (2 : ZMod 7) • Data.m33 := by
  unfold Data.m30 Data.gen3 Data.m33
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_31_0 : Data.m31 * Data.gen0 = (4 : ZMod 7) • Data.m67 := by
  unfold Data.m31 Data.gen0 Data.m67
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_31_1 : Data.m31 * Data.gen1 = (1 : ZMod 7) • Data.m7 := by
  unfold Data.m31 Data.gen1 Data.m7
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_31_2 : Data.m31 * Data.gen2 = (2 : ZMod 7) • Data.m32 := by
  unfold Data.m31 Data.gen2 Data.m32
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_31_3 : Data.m31 * Data.gen3 = (1 : ZMod 7) • Data.m25 := by
  unfold Data.m31 Data.gen3 Data.m25
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_32_0 : Data.m32 * Data.gen0 = (4 : ZMod 7) • Data.m68 := by
  unfold Data.m32 Data.gen0 Data.m68
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_32_1 : Data.m32 * Data.gen1 = (1 : ZMod 7) • Data.m8 := by
  unfold Data.m32 Data.gen1 Data.m8
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_32_2 : Data.m32 * Data.gen2 = (2 : ZMod 7) • Data.m31 := by
  unfold Data.m32 Data.gen2 Data.m31
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_32_3 : Data.m32 * Data.gen3 = (1 : ZMod 7) • Data.m34 := by
  unfold Data.m32 Data.gen3 Data.m34
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_33_0 : Data.m33 * Data.gen0 = (4 : ZMod 7) • Data.m69 := by
  unfold Data.m33 Data.gen0 Data.m69
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_33_1 : Data.m33 * Data.gen1 = (1 : ZMod 7) • Data.m9 := by
  unfold Data.m33 Data.gen1 Data.m9
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_33_2 : Data.m33 * Data.gen2 = (4 : ZMod 7) • Data.m29 := by
  unfold Data.m33 Data.gen2 Data.m29
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_33_3 : Data.m33 * Data.gen3 = (1 : ZMod 7) • Data.m35 := by
  unfold Data.m33 Data.gen3 Data.m35
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_34_0 : Data.m34 * Data.gen0 = (4 : ZMod 7) • Data.m70 := by
  unfold Data.m34 Data.gen0 Data.m70
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_34_1 : Data.m34 * Data.gen1 = (1 : ZMod 7) • Data.m10 := by
  unfold Data.m34 Data.gen1 Data.m10
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_34_2 : Data.m34 * Data.gen2 = (2 : ZMod 7) • Data.m35 := by
  unfold Data.m34 Data.gen2 Data.m35
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_34_3 : Data.m34 * Data.gen3 = (1 : ZMod 7) • Data.m28 := by
  unfold Data.m34 Data.gen3 Data.m28
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_35_0 : Data.m35 * Data.gen0 = (4 : ZMod 7) • Data.m71 := by
  unfold Data.m35 Data.gen0 Data.m71
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_35_1 : Data.m35 * Data.gen1 = (1 : ZMod 7) • Data.m11 := by
  unfold Data.m35 Data.gen1 Data.m11
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_35_2 : Data.m35 * Data.gen2 = (2 : ZMod 7) • Data.m34 := by
  unfold Data.m35 Data.gen2 Data.m34
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_35_3 : Data.m35 * Data.gen3 = (4 : ZMod 7) • Data.m30 := by
  unfold Data.m35 Data.gen3 Data.m30
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
public theorem transitions_0_2 (k : Fin 12) (i : Fin 4) :
    Data.table ((0, 2), k) * Data.generatorMatrix i =
      Data.scalar ((0, 2), k) i • Data.table (next ((0, 2), k) i) := by
  fin_cases k <;> fin_cases i
  · exact product_24_0
  · exact product_24_1
  · exact product_24_2
  · exact product_24_3
  · exact product_25_0
  · exact product_25_1
  · exact product_25_2
  · exact product_25_3
  · exact product_26_0
  · exact product_26_1
  · exact product_26_2
  · exact product_26_3
  · exact product_27_0
  · exact product_27_1
  · exact product_27_2
  · exact product_27_3
  · exact product_28_0
  · exact product_28_1
  · exact product_28_2
  · exact product_28_3
  · exact product_29_0
  · exact product_29_1
  · exact product_29_2
  · exact product_29_3
  · exact product_30_0
  · exact product_30_1
  · exact product_30_2
  · exact product_30_3
  · exact product_31_0
  · exact product_31_1
  · exact product_31_2
  · exact product_31_3
  · exact product_32_0
  · exact product_32_1
  · exact product_32_2
  · exact product_32_3
  · exact product_33_0
  · exact product_33_1
  · exact product_33_2
  · exact product_33_3
  · exact product_34_0
  · exact product_34_1
  · exact product_34_2
  · exact product_34_3
  · exact product_35_0
  · exact product_35_1
  · exact product_35_2
  · exact product_35_3

end ONan.E9A4.MatrixTable

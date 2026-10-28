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
private theorem product_84_0 : Data.m84 * Data.gen0 = (2 : ZMod 7) • Data.m12 := by
  unfold Data.m84 Data.gen0 Data.m12
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_84_1 : Data.m84 * Data.gen1 = (1 : ZMod 7) • Data.m96 := by
  unfold Data.m84 Data.gen1 Data.m96
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_84_2 : Data.m84 * Data.gen2 = (1 : ZMod 7) • Data.m85 := by
  unfold Data.m84 Data.gen2 Data.m85
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_84_3 : Data.m84 * Data.gen3 = (1 : ZMod 7) • Data.m86 := by
  unfold Data.m84 Data.gen3 Data.m86
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_85_0 : Data.m85 * Data.gen0 = (2 : ZMod 7) • Data.m13 := by
  unfold Data.m85 Data.gen0 Data.m13
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_85_1 : Data.m85 * Data.gen1 = (1 : ZMod 7) • Data.m97 := by
  unfold Data.m85 Data.gen1 Data.m97
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_85_2 : Data.m85 * Data.gen2 = (4 : ZMod 7) • Data.m84 := by
  unfold Data.m85 Data.gen2 Data.m84
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_85_3 : Data.m85 * Data.gen3 = (1 : ZMod 7) • Data.m87 := by
  unfold Data.m85 Data.gen3 Data.m87
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_86_0 : Data.m86 * Data.gen0 = (2 : ZMod 7) • Data.m14 := by
  unfold Data.m86 Data.gen0 Data.m14
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_86_1 : Data.m86 * Data.gen1 = (1 : ZMod 7) • Data.m98 := by
  unfold Data.m86 Data.gen1 Data.m98
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_86_2 : Data.m86 * Data.gen2 = (1 : ZMod 7) • Data.m88 := by
  unfold Data.m86 Data.gen2 Data.m88
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_86_3 : Data.m86 * Data.gen3 = (1 : ZMod 7) • Data.m89 := by
  unfold Data.m86 Data.gen3 Data.m89
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_87_0 : Data.m87 * Data.gen0 = (2 : ZMod 7) • Data.m15 := by
  unfold Data.m87 Data.gen0 Data.m15
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_87_1 : Data.m87 * Data.gen1 = (1 : ZMod 7) • Data.m99 := by
  unfold Data.m87 Data.gen1 Data.m99
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_87_2 : Data.m87 * Data.gen2 = (1 : ZMod 7) • Data.m90 := by
  unfold Data.m87 Data.gen2 Data.m90
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_87_3 : Data.m87 * Data.gen3 = (1 : ZMod 7) • Data.m91 := by
  unfold Data.m87 Data.gen3 Data.m91
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_88_0 : Data.m88 * Data.gen0 = (2 : ZMod 7) • Data.m16 := by
  unfold Data.m88 Data.gen0 Data.m16
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_88_1 : Data.m88 * Data.gen1 = (1 : ZMod 7) • Data.m100 := by
  unfold Data.m88 Data.gen1 Data.m100
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_88_2 : Data.m88 * Data.gen2 = (4 : ZMod 7) • Data.m86 := by
  unfold Data.m88 Data.gen2 Data.m86
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_88_3 : Data.m88 * Data.gen3 = (1 : ZMod 7) • Data.m92 := by
  unfold Data.m88 Data.gen3 Data.m92
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_89_0 : Data.m89 * Data.gen0 = (2 : ZMod 7) • Data.m17 := by
  unfold Data.m89 Data.gen0 Data.m17
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_89_1 : Data.m89 * Data.gen1 = (1 : ZMod 7) • Data.m101 := by
  unfold Data.m89 Data.gen1 Data.m101
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_89_2 : Data.m89 * Data.gen2 = (1 : ZMod 7) • Data.m93 := by
  unfold Data.m89 Data.gen2 Data.m93
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_89_3 : Data.m89 * Data.gen3 = (1 : ZMod 7) • Data.m84 := by
  unfold Data.m89 Data.gen3 Data.m84
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_90_0 : Data.m90 * Data.gen0 = (2 : ZMod 7) • Data.m18 := by
  unfold Data.m90 Data.gen0 Data.m18
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_90_1 : Data.m90 * Data.gen1 = (1 : ZMod 7) • Data.m102 := by
  unfold Data.m90 Data.gen1 Data.m102
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_90_2 : Data.m90 * Data.gen2 = (4 : ZMod 7) • Data.m87 := by
  unfold Data.m90 Data.gen2 Data.m87
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_90_3 : Data.m90 * Data.gen3 = (2 : ZMod 7) • Data.m93 := by
  unfold Data.m90 Data.gen3 Data.m93
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_91_0 : Data.m91 * Data.gen0 = (2 : ZMod 7) • Data.m19 := by
  unfold Data.m91 Data.gen0 Data.m19
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_91_1 : Data.m91 * Data.gen1 = (1 : ZMod 7) • Data.m103 := by
  unfold Data.m91 Data.gen1 Data.m103
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_91_2 : Data.m91 * Data.gen2 = (2 : ZMod 7) • Data.m92 := by
  unfold Data.m91 Data.gen2 Data.m92
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_91_3 : Data.m91 * Data.gen3 = (1 : ZMod 7) • Data.m85 := by
  unfold Data.m91 Data.gen3 Data.m85
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_92_0 : Data.m92 * Data.gen0 = (2 : ZMod 7) • Data.m20 := by
  unfold Data.m92 Data.gen0 Data.m20
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_92_1 : Data.m92 * Data.gen1 = (1 : ZMod 7) • Data.m104 := by
  unfold Data.m92 Data.gen1 Data.m104
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_92_2 : Data.m92 * Data.gen2 = (2 : ZMod 7) • Data.m91 := by
  unfold Data.m92 Data.gen2 Data.m91
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_92_3 : Data.m92 * Data.gen3 = (1 : ZMod 7) • Data.m94 := by
  unfold Data.m92 Data.gen3 Data.m94
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_93_0 : Data.m93 * Data.gen0 = (2 : ZMod 7) • Data.m21 := by
  unfold Data.m93 Data.gen0 Data.m21
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_93_1 : Data.m93 * Data.gen1 = (1 : ZMod 7) • Data.m105 := by
  unfold Data.m93 Data.gen1 Data.m105
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_93_2 : Data.m93 * Data.gen2 = (4 : ZMod 7) • Data.m89 := by
  unfold Data.m93 Data.gen2 Data.m89
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_93_3 : Data.m93 * Data.gen3 = (1 : ZMod 7) • Data.m95 := by
  unfold Data.m93 Data.gen3 Data.m95
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_94_0 : Data.m94 * Data.gen0 = (2 : ZMod 7) • Data.m22 := by
  unfold Data.m94 Data.gen0 Data.m22
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_94_1 : Data.m94 * Data.gen1 = (1 : ZMod 7) • Data.m106 := by
  unfold Data.m94 Data.gen1 Data.m106
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_94_2 : Data.m94 * Data.gen2 = (2 : ZMod 7) • Data.m95 := by
  unfold Data.m94 Data.gen2 Data.m95
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_94_3 : Data.m94 * Data.gen3 = (1 : ZMod 7) • Data.m88 := by
  unfold Data.m94 Data.gen3 Data.m88
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_95_0 : Data.m95 * Data.gen0 = (2 : ZMod 7) • Data.m23 := by
  unfold Data.m95 Data.gen0 Data.m23
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_95_1 : Data.m95 * Data.gen1 = (1 : ZMod 7) • Data.m107 := by
  unfold Data.m95 Data.gen1 Data.m107
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_95_2 : Data.m95 * Data.gen2 = (2 : ZMod 7) • Data.m94 := by
  unfold Data.m95 Data.gen2 Data.m94
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_95_3 : Data.m95 * Data.gen3 = (4 : ZMod 7) • Data.m90 := by
  unfold Data.m95 Data.gen3 Data.m90
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
public theorem transitions_2_1 (k : Fin 12) (i : Fin 4) :
    Data.table ((2, 1), k) * Data.generatorMatrix i =
      Data.scalar ((2, 1), k) i • Data.table (next ((2, 1), k) i) := by
  fin_cases k <;> fin_cases i
  · exact product_84_0
  · exact product_84_1
  · exact product_84_2
  · exact product_84_3
  · exact product_85_0
  · exact product_85_1
  · exact product_85_2
  · exact product_85_3
  · exact product_86_0
  · exact product_86_1
  · exact product_86_2
  · exact product_86_3
  · exact product_87_0
  · exact product_87_1
  · exact product_87_2
  · exact product_87_3
  · exact product_88_0
  · exact product_88_1
  · exact product_88_2
  · exact product_88_3
  · exact product_89_0
  · exact product_89_1
  · exact product_89_2
  · exact product_89_3
  · exact product_90_0
  · exact product_90_1
  · exact product_90_2
  · exact product_90_3
  · exact product_91_0
  · exact product_91_1
  · exact product_91_2
  · exact product_91_3
  · exact product_92_0
  · exact product_92_1
  · exact product_92_2
  · exact product_92_3
  · exact product_93_0
  · exact product_93_1
  · exact product_93_2
  · exact product_93_3
  · exact product_94_0
  · exact product_94_1
  · exact product_94_2
  · exact product_94_3
  · exact product_95_0
  · exact product_95_1
  · exact product_95_2
  · exact product_95_3

end ONan.E9A4.MatrixTable

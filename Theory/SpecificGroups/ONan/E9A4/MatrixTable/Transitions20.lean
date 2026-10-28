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
private theorem product_72_0 : Data.m72 * Data.gen0 = (1 : ZMod 7) • Data.m0 := by
  unfold Data.m72 Data.gen0 Data.m0
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_72_1 : Data.m72 * Data.gen1 = (1 : ZMod 7) • Data.m84 := by
  unfold Data.m72 Data.gen1 Data.m84
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_72_2 : Data.m72 * Data.gen2 = (1 : ZMod 7) • Data.m73 := by
  unfold Data.m72 Data.gen2 Data.m73
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_72_3 : Data.m72 * Data.gen3 = (1 : ZMod 7) • Data.m74 := by
  unfold Data.m72 Data.gen3 Data.m74
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_73_0 : Data.m73 * Data.gen0 = (1 : ZMod 7) • Data.m1 := by
  unfold Data.m73 Data.gen0 Data.m1
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_73_1 : Data.m73 * Data.gen1 = (1 : ZMod 7) • Data.m85 := by
  unfold Data.m73 Data.gen1 Data.m85
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_73_2 : Data.m73 * Data.gen2 = (4 : ZMod 7) • Data.m72 := by
  unfold Data.m73 Data.gen2 Data.m72
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_73_3 : Data.m73 * Data.gen3 = (1 : ZMod 7) • Data.m75 := by
  unfold Data.m73 Data.gen3 Data.m75
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_74_0 : Data.m74 * Data.gen0 = (1 : ZMod 7) • Data.m2 := by
  unfold Data.m74 Data.gen0 Data.m2
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_74_1 : Data.m74 * Data.gen1 = (1 : ZMod 7) • Data.m86 := by
  unfold Data.m74 Data.gen1 Data.m86
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_74_2 : Data.m74 * Data.gen2 = (1 : ZMod 7) • Data.m76 := by
  unfold Data.m74 Data.gen2 Data.m76
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_74_3 : Data.m74 * Data.gen3 = (1 : ZMod 7) • Data.m77 := by
  unfold Data.m74 Data.gen3 Data.m77
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_75_0 : Data.m75 * Data.gen0 = (1 : ZMod 7) • Data.m3 := by
  unfold Data.m75 Data.gen0 Data.m3
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_75_1 : Data.m75 * Data.gen1 = (1 : ZMod 7) • Data.m87 := by
  unfold Data.m75 Data.gen1 Data.m87
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_75_2 : Data.m75 * Data.gen2 = (1 : ZMod 7) • Data.m78 := by
  unfold Data.m75 Data.gen2 Data.m78
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_75_3 : Data.m75 * Data.gen3 = (1 : ZMod 7) • Data.m79 := by
  unfold Data.m75 Data.gen3 Data.m79
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_76_0 : Data.m76 * Data.gen0 = (1 : ZMod 7) • Data.m4 := by
  unfold Data.m76 Data.gen0 Data.m4
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_76_1 : Data.m76 * Data.gen1 = (1 : ZMod 7) • Data.m88 := by
  unfold Data.m76 Data.gen1 Data.m88
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_76_2 : Data.m76 * Data.gen2 = (4 : ZMod 7) • Data.m74 := by
  unfold Data.m76 Data.gen2 Data.m74
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_76_3 : Data.m76 * Data.gen3 = (1 : ZMod 7) • Data.m80 := by
  unfold Data.m76 Data.gen3 Data.m80
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_77_0 : Data.m77 * Data.gen0 = (1 : ZMod 7) • Data.m5 := by
  unfold Data.m77 Data.gen0 Data.m5
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_77_1 : Data.m77 * Data.gen1 = (1 : ZMod 7) • Data.m89 := by
  unfold Data.m77 Data.gen1 Data.m89
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_77_2 : Data.m77 * Data.gen2 = (1 : ZMod 7) • Data.m81 := by
  unfold Data.m77 Data.gen2 Data.m81
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_77_3 : Data.m77 * Data.gen3 = (1 : ZMod 7) • Data.m72 := by
  unfold Data.m77 Data.gen3 Data.m72
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_78_0 : Data.m78 * Data.gen0 = (1 : ZMod 7) • Data.m6 := by
  unfold Data.m78 Data.gen0 Data.m6
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_78_1 : Data.m78 * Data.gen1 = (1 : ZMod 7) • Data.m90 := by
  unfold Data.m78 Data.gen1 Data.m90
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_78_2 : Data.m78 * Data.gen2 = (4 : ZMod 7) • Data.m75 := by
  unfold Data.m78 Data.gen2 Data.m75
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_78_3 : Data.m78 * Data.gen3 = (2 : ZMod 7) • Data.m81 := by
  unfold Data.m78 Data.gen3 Data.m81
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_79_0 : Data.m79 * Data.gen0 = (1 : ZMod 7) • Data.m7 := by
  unfold Data.m79 Data.gen0 Data.m7
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_79_1 : Data.m79 * Data.gen1 = (1 : ZMod 7) • Data.m91 := by
  unfold Data.m79 Data.gen1 Data.m91
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_79_2 : Data.m79 * Data.gen2 = (2 : ZMod 7) • Data.m80 := by
  unfold Data.m79 Data.gen2 Data.m80
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_79_3 : Data.m79 * Data.gen3 = (1 : ZMod 7) • Data.m73 := by
  unfold Data.m79 Data.gen3 Data.m73
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_80_0 : Data.m80 * Data.gen0 = (1 : ZMod 7) • Data.m8 := by
  unfold Data.m80 Data.gen0 Data.m8
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_80_1 : Data.m80 * Data.gen1 = (1 : ZMod 7) • Data.m92 := by
  unfold Data.m80 Data.gen1 Data.m92
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_80_2 : Data.m80 * Data.gen2 = (2 : ZMod 7) • Data.m79 := by
  unfold Data.m80 Data.gen2 Data.m79
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_80_3 : Data.m80 * Data.gen3 = (1 : ZMod 7) • Data.m82 := by
  unfold Data.m80 Data.gen3 Data.m82
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_81_0 : Data.m81 * Data.gen0 = (1 : ZMod 7) • Data.m9 := by
  unfold Data.m81 Data.gen0 Data.m9
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_81_1 : Data.m81 * Data.gen1 = (1 : ZMod 7) • Data.m93 := by
  unfold Data.m81 Data.gen1 Data.m93
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_81_2 : Data.m81 * Data.gen2 = (4 : ZMod 7) • Data.m77 := by
  unfold Data.m81 Data.gen2 Data.m77
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_81_3 : Data.m81 * Data.gen3 = (1 : ZMod 7) • Data.m83 := by
  unfold Data.m81 Data.gen3 Data.m83
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_82_0 : Data.m82 * Data.gen0 = (1 : ZMod 7) • Data.m10 := by
  unfold Data.m82 Data.gen0 Data.m10
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_82_1 : Data.m82 * Data.gen1 = (1 : ZMod 7) • Data.m94 := by
  unfold Data.m82 Data.gen1 Data.m94
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_82_2 : Data.m82 * Data.gen2 = (2 : ZMod 7) • Data.m83 := by
  unfold Data.m82 Data.gen2 Data.m83
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_82_3 : Data.m82 * Data.gen3 = (1 : ZMod 7) • Data.m76 := by
  unfold Data.m82 Data.gen3 Data.m76
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_83_0 : Data.m83 * Data.gen0 = (1 : ZMod 7) • Data.m11 := by
  unfold Data.m83 Data.gen0 Data.m11
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_83_1 : Data.m83 * Data.gen1 = (1 : ZMod 7) • Data.m95 := by
  unfold Data.m83 Data.gen1 Data.m95
  exact checkScaled_sound _ _ _ 1 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_83_2 : Data.m83 * Data.gen2 = (2 : ZMod 7) • Data.m82 := by
  unfold Data.m83 Data.gen2 Data.m82
  exact checkScaled_sound _ _ _ 2 (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem product_83_3 : Data.m83 * Data.gen3 = (4 : ZMod 7) • Data.m78 := by
  unfold Data.m83 Data.gen3 Data.m78
  exact checkScaled_sound _ _ _ 4 (by decide +kernel)

set_option maxRecDepth 4096 in
public theorem transitions_2_0 (k : Fin 12) (i : Fin 4) :
    Data.table ((2, 0), k) * Data.generatorMatrix i =
      Data.scalar ((2, 0), k) i • Data.table (next ((2, 0), k) i) := by
  fin_cases k <;> fin_cases i
  · exact product_72_0
  · exact product_72_1
  · exact product_72_2
  · exact product_72_3
  · exact product_73_0
  · exact product_73_1
  · exact product_73_2
  · exact product_73_3
  · exact product_74_0
  · exact product_74_1
  · exact product_74_2
  · exact product_74_3
  · exact product_75_0
  · exact product_75_1
  · exact product_75_2
  · exact product_75_3
  · exact product_76_0
  · exact product_76_1
  · exact product_76_2
  · exact product_76_3
  · exact product_77_0
  · exact product_77_1
  · exact product_77_2
  · exact product_77_3
  · exact product_78_0
  · exact product_78_1
  · exact product_78_2
  · exact product_78_3
  · exact product_79_0
  · exact product_79_1
  · exact product_79_2
  · exact product_79_3
  · exact product_80_0
  · exact product_80_1
  · exact product_80_2
  · exact product_80_3
  · exact product_81_0
  · exact product_81_1
  · exact product_81_2
  · exact product_81_3
  · exact product_82_0
  · exact product_82_1
  · exact product_82_2
  · exact product_82_3
  · exact product_83_0
  · exact product_83_1
  · exact product_83_2
  · exact product_83_3

end ONan.E9A4.MatrixTable

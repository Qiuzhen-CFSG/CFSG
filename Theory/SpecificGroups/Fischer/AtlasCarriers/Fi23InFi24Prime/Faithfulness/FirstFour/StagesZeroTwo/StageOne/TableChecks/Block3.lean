module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.Setup

/-!
# Stage-one finite checks on [12288, 16384)

Ordinary kernel reduction checks 128 vertices per leaf. The leaves are joined
without repeating their reductions. At most 32 leaves share a compiler process.
Source: `source/tree.json`, ATLAS F24G1-p306936B0; GLS3 Table 5.3v.
Regenerate with `source/emit_checks.py`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne
open Certificate

private theorem leaf96 : checkPow localTest 12288 7 = true := by
  decide +kernel

private theorem leaf97 : checkPow localTest 12416 7 = true := by
  decide +kernel

private theorem leaf98 : checkPow localTest 12544 7 = true := by
  decide +kernel

private theorem leaf99 : checkPow localTest 12672 7 = true := by
  decide +kernel

private theorem leaf100 : checkPow localTest 12800 7 = true := by
  decide +kernel

private theorem leaf101 : checkPow localTest 12928 7 = true := by
  decide +kernel

private theorem leaf102 : checkPow localTest 13056 7 = true := by
  decide +kernel

private theorem leaf103 : checkPow localTest 13184 7 = true := by
  decide +kernel

private theorem leaf104 : checkPow localTest 13312 7 = true := by
  decide +kernel

private theorem leaf105 : checkPow localTest 13440 7 = true := by
  decide +kernel

private theorem leaf106 : checkPow localTest 13568 7 = true := by
  decide +kernel

private theorem leaf107 : checkPow localTest 13696 7 = true := by
  decide +kernel

private theorem leaf108 : checkPow localTest 13824 7 = true := by
  decide +kernel

private theorem leaf109 : checkPow localTest 13952 7 = true := by
  decide +kernel

private theorem leaf110 : checkPow localTest 14080 7 = true := by
  decide +kernel

private theorem leaf111 : checkPow localTest 14208 7 = true := by
  decide +kernel

private theorem leaf112 : checkPow localTest 14336 7 = true := by
  decide +kernel

private theorem leaf113 : checkPow localTest 14464 7 = true := by
  decide +kernel

private theorem leaf114 : checkPow localTest 14592 7 = true := by
  decide +kernel

private theorem leaf115 : checkPow localTest 14720 7 = true := by
  decide +kernel

private theorem leaf116 : checkPow localTest 14848 7 = true := by
  decide +kernel

private theorem leaf117 : checkPow localTest 14976 7 = true := by
  decide +kernel

private theorem leaf118 : checkPow localTest 15104 7 = true := by
  decide +kernel

private theorem leaf119 : checkPow localTest 15232 7 = true := by
  decide +kernel

private theorem leaf120 : checkPow localTest 15360 7 = true := by
  decide +kernel

private theorem leaf121 : checkPow localTest 15488 7 = true := by
  decide +kernel

private theorem leaf122 : checkPow localTest 15616 7 = true := by
  decide +kernel

private theorem leaf123 : checkPow localTest 15744 7 = true := by
  decide +kernel

private theorem leaf124 : checkPow localTest 15872 7 = true := by
  decide +kernel

private theorem leaf125 : checkPow localTest 16000 7 = true := by
  decide +kernel

private theorem leaf126 : checkPow localTest 16128 7 = true := by
  decide +kernel

private theorem leaf127 : checkPow localTest 16256 7 = true := by
  decide +kernel

private theorem joined12288_8 : checkPow localTest 12288 8 = true :=
  checkPow_join localTest 7 12288 leaf96 leaf97

private theorem joined12544_8 : checkPow localTest 12544 8 = true :=
  checkPow_join localTest 7 12544 leaf98 leaf99

private theorem joined12288_9 : checkPow localTest 12288 9 = true :=
  checkPow_join localTest 8 12288 joined12288_8 joined12544_8

private theorem joined12800_8 : checkPow localTest 12800 8 = true :=
  checkPow_join localTest 7 12800 leaf100 leaf101

private theorem joined13056_8 : checkPow localTest 13056 8 = true :=
  checkPow_join localTest 7 13056 leaf102 leaf103

private theorem joined12800_9 : checkPow localTest 12800 9 = true :=
  checkPow_join localTest 8 12800 joined12800_8 joined13056_8

private theorem joined12288_10 : checkPow localTest 12288 10 = true :=
  checkPow_join localTest 9 12288 joined12288_9 joined12800_9

private theorem joined13312_8 : checkPow localTest 13312 8 = true :=
  checkPow_join localTest 7 13312 leaf104 leaf105

private theorem joined13568_8 : checkPow localTest 13568 8 = true :=
  checkPow_join localTest 7 13568 leaf106 leaf107

private theorem joined13312_9 : checkPow localTest 13312 9 = true :=
  checkPow_join localTest 8 13312 joined13312_8 joined13568_8

private theorem joined13824_8 : checkPow localTest 13824 8 = true :=
  checkPow_join localTest 7 13824 leaf108 leaf109

private theorem joined14080_8 : checkPow localTest 14080 8 = true :=
  checkPow_join localTest 7 14080 leaf110 leaf111

private theorem joined13824_9 : checkPow localTest 13824 9 = true :=
  checkPow_join localTest 8 13824 joined13824_8 joined14080_8

private theorem joined13312_10 : checkPow localTest 13312 10 = true :=
  checkPow_join localTest 9 13312 joined13312_9 joined13824_9

private theorem joined12288_11 : checkPow localTest 12288 11 = true :=
  checkPow_join localTest 10 12288 joined12288_10 joined13312_10

private theorem joined14336_8 : checkPow localTest 14336 8 = true :=
  checkPow_join localTest 7 14336 leaf112 leaf113

private theorem joined14592_8 : checkPow localTest 14592 8 = true :=
  checkPow_join localTest 7 14592 leaf114 leaf115

private theorem joined14336_9 : checkPow localTest 14336 9 = true :=
  checkPow_join localTest 8 14336 joined14336_8 joined14592_8

private theorem joined14848_8 : checkPow localTest 14848 8 = true :=
  checkPow_join localTest 7 14848 leaf116 leaf117

private theorem joined15104_8 : checkPow localTest 15104 8 = true :=
  checkPow_join localTest 7 15104 leaf118 leaf119

private theorem joined14848_9 : checkPow localTest 14848 9 = true :=
  checkPow_join localTest 8 14848 joined14848_8 joined15104_8

private theorem joined14336_10 : checkPow localTest 14336 10 = true :=
  checkPow_join localTest 9 14336 joined14336_9 joined14848_9

private theorem joined15360_8 : checkPow localTest 15360 8 = true :=
  checkPow_join localTest 7 15360 leaf120 leaf121

private theorem joined15616_8 : checkPow localTest 15616 8 = true :=
  checkPow_join localTest 7 15616 leaf122 leaf123

private theorem joined15360_9 : checkPow localTest 15360 9 = true :=
  checkPow_join localTest 8 15360 joined15360_8 joined15616_8

private theorem joined15872_8 : checkPow localTest 15872 8 = true :=
  checkPow_join localTest 7 15872 leaf124 leaf125

private theorem joined16128_8 : checkPow localTest 16128 8 = true :=
  checkPow_join localTest 7 16128 leaf126 leaf127

private theorem joined15872_9 : checkPow localTest 15872 9 = true :=
  checkPow_join localTest 8 15872 joined15872_8 joined16128_8

private theorem joined15360_10 : checkPow localTest 15360 10 = true :=
  checkPow_join localTest 9 15360 joined15360_9 joined15872_9

private theorem joined14336_11 : checkPow localTest 14336 11 = true :=
  checkPow_join localTest 10 14336 joined14336_10 joined15360_10

private theorem joined12288_12 : checkPow localTest 12288 12 = true :=
  checkPow_join localTest 11 12288 joined12288_11 joined14336_11

theorem range3_checked (n : Nat) (hn : 12288 ≤ n) (hm : n < 16384) :
    localTest n = true :=
  checkPow_sound localTest 12 12288 joined12288_12 n hn hm

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne

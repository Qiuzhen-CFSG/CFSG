module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.Setup

/-!
# Stage-one finite checks on [4096, 8192)

Ordinary kernel reduction checks 128 vertices per leaf. The leaves are joined
without repeating their reductions. At most 32 leaves share a compiler process.
Source: `source/tree.json`, ATLAS F24G1-p306936B0; GLS3 Table 5.3v.
Regenerate with `source/emit_checks.py`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne
open Certificate

private theorem leaf32 : checkPow localTest 4096 7 = true := by
  decide +kernel

private theorem leaf33 : checkPow localTest 4224 7 = true := by
  decide +kernel

private theorem leaf34 : checkPow localTest 4352 7 = true := by
  decide +kernel

private theorem leaf35 : checkPow localTest 4480 7 = true := by
  decide +kernel

private theorem leaf36 : checkPow localTest 4608 7 = true := by
  decide +kernel

private theorem leaf37 : checkPow localTest 4736 7 = true := by
  decide +kernel

private theorem leaf38 : checkPow localTest 4864 7 = true := by
  decide +kernel

private theorem leaf39 : checkPow localTest 4992 7 = true := by
  decide +kernel

private theorem leaf40 : checkPow localTest 5120 7 = true := by
  decide +kernel

private theorem leaf41 : checkPow localTest 5248 7 = true := by
  decide +kernel

private theorem leaf42 : checkPow localTest 5376 7 = true := by
  decide +kernel

private theorem leaf43 : checkPow localTest 5504 7 = true := by
  decide +kernel

private theorem leaf44 : checkPow localTest 5632 7 = true := by
  decide +kernel

private theorem leaf45 : checkPow localTest 5760 7 = true := by
  decide +kernel

private theorem leaf46 : checkPow localTest 5888 7 = true := by
  decide +kernel

private theorem leaf47 : checkPow localTest 6016 7 = true := by
  decide +kernel

private theorem leaf48 : checkPow localTest 6144 7 = true := by
  decide +kernel

private theorem leaf49 : checkPow localTest 6272 7 = true := by
  decide +kernel

private theorem leaf50 : checkPow localTest 6400 7 = true := by
  decide +kernel

private theorem leaf51 : checkPow localTest 6528 7 = true := by
  decide +kernel

private theorem leaf52 : checkPow localTest 6656 7 = true := by
  decide +kernel

private theorem leaf53 : checkPow localTest 6784 7 = true := by
  decide +kernel

private theorem leaf54 : checkPow localTest 6912 7 = true := by
  decide +kernel

private theorem leaf55 : checkPow localTest 7040 7 = true := by
  decide +kernel

private theorem leaf56 : checkPow localTest 7168 7 = true := by
  decide +kernel

private theorem leaf57 : checkPow localTest 7296 7 = true := by
  decide +kernel

private theorem leaf58 : checkPow localTest 7424 7 = true := by
  decide +kernel

private theorem leaf59 : checkPow localTest 7552 7 = true := by
  decide +kernel

private theorem leaf60 : checkPow localTest 7680 7 = true := by
  decide +kernel

private theorem leaf61 : checkPow localTest 7808 7 = true := by
  decide +kernel

private theorem leaf62 : checkPow localTest 7936 7 = true := by
  decide +kernel

private theorem leaf63 : checkPow localTest 8064 7 = true := by
  decide +kernel

private theorem joined4096_8 : checkPow localTest 4096 8 = true :=
  checkPow_join localTest 7 4096 leaf32 leaf33

private theorem joined4352_8 : checkPow localTest 4352 8 = true :=
  checkPow_join localTest 7 4352 leaf34 leaf35

private theorem joined4096_9 : checkPow localTest 4096 9 = true :=
  checkPow_join localTest 8 4096 joined4096_8 joined4352_8

private theorem joined4608_8 : checkPow localTest 4608 8 = true :=
  checkPow_join localTest 7 4608 leaf36 leaf37

private theorem joined4864_8 : checkPow localTest 4864 8 = true :=
  checkPow_join localTest 7 4864 leaf38 leaf39

private theorem joined4608_9 : checkPow localTest 4608 9 = true :=
  checkPow_join localTest 8 4608 joined4608_8 joined4864_8

private theorem joined4096_10 : checkPow localTest 4096 10 = true :=
  checkPow_join localTest 9 4096 joined4096_9 joined4608_9

private theorem joined5120_8 : checkPow localTest 5120 8 = true :=
  checkPow_join localTest 7 5120 leaf40 leaf41

private theorem joined5376_8 : checkPow localTest 5376 8 = true :=
  checkPow_join localTest 7 5376 leaf42 leaf43

private theorem joined5120_9 : checkPow localTest 5120 9 = true :=
  checkPow_join localTest 8 5120 joined5120_8 joined5376_8

private theorem joined5632_8 : checkPow localTest 5632 8 = true :=
  checkPow_join localTest 7 5632 leaf44 leaf45

private theorem joined5888_8 : checkPow localTest 5888 8 = true :=
  checkPow_join localTest 7 5888 leaf46 leaf47

private theorem joined5632_9 : checkPow localTest 5632 9 = true :=
  checkPow_join localTest 8 5632 joined5632_8 joined5888_8

private theorem joined5120_10 : checkPow localTest 5120 10 = true :=
  checkPow_join localTest 9 5120 joined5120_9 joined5632_9

private theorem joined4096_11 : checkPow localTest 4096 11 = true :=
  checkPow_join localTest 10 4096 joined4096_10 joined5120_10

private theorem joined6144_8 : checkPow localTest 6144 8 = true :=
  checkPow_join localTest 7 6144 leaf48 leaf49

private theorem joined6400_8 : checkPow localTest 6400 8 = true :=
  checkPow_join localTest 7 6400 leaf50 leaf51

private theorem joined6144_9 : checkPow localTest 6144 9 = true :=
  checkPow_join localTest 8 6144 joined6144_8 joined6400_8

private theorem joined6656_8 : checkPow localTest 6656 8 = true :=
  checkPow_join localTest 7 6656 leaf52 leaf53

private theorem joined6912_8 : checkPow localTest 6912 8 = true :=
  checkPow_join localTest 7 6912 leaf54 leaf55

private theorem joined6656_9 : checkPow localTest 6656 9 = true :=
  checkPow_join localTest 8 6656 joined6656_8 joined6912_8

private theorem joined6144_10 : checkPow localTest 6144 10 = true :=
  checkPow_join localTest 9 6144 joined6144_9 joined6656_9

private theorem joined7168_8 : checkPow localTest 7168 8 = true :=
  checkPow_join localTest 7 7168 leaf56 leaf57

private theorem joined7424_8 : checkPow localTest 7424 8 = true :=
  checkPow_join localTest 7 7424 leaf58 leaf59

private theorem joined7168_9 : checkPow localTest 7168 9 = true :=
  checkPow_join localTest 8 7168 joined7168_8 joined7424_8

private theorem joined7680_8 : checkPow localTest 7680 8 = true :=
  checkPow_join localTest 7 7680 leaf60 leaf61

private theorem joined7936_8 : checkPow localTest 7936 8 = true :=
  checkPow_join localTest 7 7936 leaf62 leaf63

private theorem joined7680_9 : checkPow localTest 7680 9 = true :=
  checkPow_join localTest 8 7680 joined7680_8 joined7936_8

private theorem joined7168_10 : checkPow localTest 7168 10 = true :=
  checkPow_join localTest 9 7168 joined7168_9 joined7680_9

private theorem joined6144_11 : checkPow localTest 6144 11 = true :=
  checkPow_join localTest 10 6144 joined6144_10 joined7168_10

private theorem joined4096_12 : checkPow localTest 4096 12 = true :=
  checkPow_join localTest 11 4096 joined4096_11 joined6144_11

theorem range1_checked (n : Nat) (hn : 4096 ≤ n) (hm : n < 8192) :
    localTest n = true :=
  checkPow_sound localTest 12 4096 joined4096_12 n hn hm

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne

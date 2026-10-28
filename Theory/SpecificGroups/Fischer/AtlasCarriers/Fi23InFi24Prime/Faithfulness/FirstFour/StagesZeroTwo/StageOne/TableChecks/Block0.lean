module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.Setup

/-!
# Stage-one finite checks on [0, 4096)

Ordinary kernel reduction checks 128 vertices per leaf. The leaves are joined
without repeating their reductions. At most 32 leaves share a compiler process.
Source: `source/tree.json`, ATLAS F24G1-p306936B0; GLS3 Table 5.3v.
Regenerate with `source/emit_checks.py`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne
open Certificate

private theorem leaf0 : checkPow localTest 0 7 = true := by
  decide +kernel

private theorem leaf1 : checkPow localTest 128 7 = true := by
  decide +kernel

private theorem leaf2 : checkPow localTest 256 7 = true := by
  decide +kernel

private theorem leaf3 : checkPow localTest 384 7 = true := by
  decide +kernel

private theorem leaf4 : checkPow localTest 512 7 = true := by
  decide +kernel

private theorem leaf5 : checkPow localTest 640 7 = true := by
  decide +kernel

private theorem leaf6 : checkPow localTest 768 7 = true := by
  decide +kernel

private theorem leaf7 : checkPow localTest 896 7 = true := by
  decide +kernel

private theorem leaf8 : checkPow localTest 1024 7 = true := by
  decide +kernel

private theorem leaf9 : checkPow localTest 1152 7 = true := by
  decide +kernel

private theorem leaf10 : checkPow localTest 1280 7 = true := by
  decide +kernel

private theorem leaf11 : checkPow localTest 1408 7 = true := by
  decide +kernel

private theorem leaf12 : checkPow localTest 1536 7 = true := by
  decide +kernel

private theorem leaf13 : checkPow localTest 1664 7 = true := by
  decide +kernel

private theorem leaf14 : checkPow localTest 1792 7 = true := by
  decide +kernel

private theorem leaf15 : checkPow localTest 1920 7 = true := by
  decide +kernel

private theorem leaf16 : checkPow localTest 2048 7 = true := by
  decide +kernel

private theorem leaf17 : checkPow localTest 2176 7 = true := by
  decide +kernel

private theorem leaf18 : checkPow localTest 2304 7 = true := by
  decide +kernel

private theorem leaf19 : checkPow localTest 2432 7 = true := by
  decide +kernel

private theorem leaf20 : checkPow localTest 2560 7 = true := by
  decide +kernel

private theorem leaf21 : checkPow localTest 2688 7 = true := by
  decide +kernel

private theorem leaf22 : checkPow localTest 2816 7 = true := by
  decide +kernel

private theorem leaf23 : checkPow localTest 2944 7 = true := by
  decide +kernel

private theorem leaf24 : checkPow localTest 3072 7 = true := by
  decide +kernel

private theorem leaf25 : checkPow localTest 3200 7 = true := by
  decide +kernel

private theorem leaf26 : checkPow localTest 3328 7 = true := by
  decide +kernel

private theorem leaf27 : checkPow localTest 3456 7 = true := by
  decide +kernel

private theorem leaf28 : checkPow localTest 3584 7 = true := by
  decide +kernel

private theorem leaf29 : checkPow localTest 3712 7 = true := by
  decide +kernel

private theorem leaf30 : checkPow localTest 3840 7 = true := by
  decide +kernel

private theorem leaf31 : checkPow localTest 3968 7 = true := by
  decide +kernel

private theorem joined0_8 : checkPow localTest 0 8 = true :=
  checkPow_join localTest 7 0 leaf0 leaf1

private theorem joined256_8 : checkPow localTest 256 8 = true :=
  checkPow_join localTest 7 256 leaf2 leaf3

private theorem joined0_9 : checkPow localTest 0 9 = true :=
  checkPow_join localTest 8 0 joined0_8 joined256_8

private theorem joined512_8 : checkPow localTest 512 8 = true :=
  checkPow_join localTest 7 512 leaf4 leaf5

private theorem joined768_8 : checkPow localTest 768 8 = true :=
  checkPow_join localTest 7 768 leaf6 leaf7

private theorem joined512_9 : checkPow localTest 512 9 = true :=
  checkPow_join localTest 8 512 joined512_8 joined768_8

private theorem joined0_10 : checkPow localTest 0 10 = true :=
  checkPow_join localTest 9 0 joined0_9 joined512_9

private theorem joined1024_8 : checkPow localTest 1024 8 = true :=
  checkPow_join localTest 7 1024 leaf8 leaf9

private theorem joined1280_8 : checkPow localTest 1280 8 = true :=
  checkPow_join localTest 7 1280 leaf10 leaf11

private theorem joined1024_9 : checkPow localTest 1024 9 = true :=
  checkPow_join localTest 8 1024 joined1024_8 joined1280_8

private theorem joined1536_8 : checkPow localTest 1536 8 = true :=
  checkPow_join localTest 7 1536 leaf12 leaf13

private theorem joined1792_8 : checkPow localTest 1792 8 = true :=
  checkPow_join localTest 7 1792 leaf14 leaf15

private theorem joined1536_9 : checkPow localTest 1536 9 = true :=
  checkPow_join localTest 8 1536 joined1536_8 joined1792_8

private theorem joined1024_10 : checkPow localTest 1024 10 = true :=
  checkPow_join localTest 9 1024 joined1024_9 joined1536_9

private theorem joined0_11 : checkPow localTest 0 11 = true :=
  checkPow_join localTest 10 0 joined0_10 joined1024_10

private theorem joined2048_8 : checkPow localTest 2048 8 = true :=
  checkPow_join localTest 7 2048 leaf16 leaf17

private theorem joined2304_8 : checkPow localTest 2304 8 = true :=
  checkPow_join localTest 7 2304 leaf18 leaf19

private theorem joined2048_9 : checkPow localTest 2048 9 = true :=
  checkPow_join localTest 8 2048 joined2048_8 joined2304_8

private theorem joined2560_8 : checkPow localTest 2560 8 = true :=
  checkPow_join localTest 7 2560 leaf20 leaf21

private theorem joined2816_8 : checkPow localTest 2816 8 = true :=
  checkPow_join localTest 7 2816 leaf22 leaf23

private theorem joined2560_9 : checkPow localTest 2560 9 = true :=
  checkPow_join localTest 8 2560 joined2560_8 joined2816_8

private theorem joined2048_10 : checkPow localTest 2048 10 = true :=
  checkPow_join localTest 9 2048 joined2048_9 joined2560_9

private theorem joined3072_8 : checkPow localTest 3072 8 = true :=
  checkPow_join localTest 7 3072 leaf24 leaf25

private theorem joined3328_8 : checkPow localTest 3328 8 = true :=
  checkPow_join localTest 7 3328 leaf26 leaf27

private theorem joined3072_9 : checkPow localTest 3072 9 = true :=
  checkPow_join localTest 8 3072 joined3072_8 joined3328_8

private theorem joined3584_8 : checkPow localTest 3584 8 = true :=
  checkPow_join localTest 7 3584 leaf28 leaf29

private theorem joined3840_8 : checkPow localTest 3840 8 = true :=
  checkPow_join localTest 7 3840 leaf30 leaf31

private theorem joined3584_9 : checkPow localTest 3584 9 = true :=
  checkPow_join localTest 8 3584 joined3584_8 joined3840_8

private theorem joined3072_10 : checkPow localTest 3072 10 = true :=
  checkPow_join localTest 9 3072 joined3072_9 joined3584_9

private theorem joined2048_11 : checkPow localTest 2048 11 = true :=
  checkPow_join localTest 10 2048 joined2048_10 joined3072_10

private theorem joined0_12 : checkPow localTest 0 12 = true :=
  checkPow_join localTest 11 0 joined0_11 joined2048_11

theorem range0_checked (n : Nat) (hn : 0 ≤ n) (hm : n < 4096) :
    localTest n = true :=
  checkPow_sound localTest 12 0 joined0_12 n hn hm

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne

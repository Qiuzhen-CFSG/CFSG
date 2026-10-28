module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.Setup

/-!
# Stage-one finite checks on [8192, 12288)

Ordinary kernel reduction checks 128 vertices per leaf. The leaves are joined
without repeating their reductions. At most 32 leaves share a compiler process.
Source: `source/tree.json`, ATLAS F24G1-p306936B0; GLS3 Table 5.3v.
Regenerate with `source/emit_checks.py`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne
open Certificate

private theorem leaf64 : checkPow localTest 8192 7 = true := by
  decide +kernel

private theorem leaf65 : checkPow localTest 8320 7 = true := by
  decide +kernel

private theorem leaf66 : checkPow localTest 8448 7 = true := by
  decide +kernel

private theorem leaf67 : checkPow localTest 8576 7 = true := by
  decide +kernel

private theorem leaf68 : checkPow localTest 8704 7 = true := by
  decide +kernel

private theorem leaf69 : checkPow localTest 8832 7 = true := by
  decide +kernel

private theorem leaf70 : checkPow localTest 8960 7 = true := by
  decide +kernel

private theorem leaf71 : checkPow localTest 9088 7 = true := by
  decide +kernel

private theorem leaf72 : checkPow localTest 9216 7 = true := by
  decide +kernel

private theorem leaf73 : checkPow localTest 9344 7 = true := by
  decide +kernel

private theorem leaf74 : checkPow localTest 9472 7 = true := by
  decide +kernel

private theorem leaf75 : checkPow localTest 9600 7 = true := by
  decide +kernel

private theorem leaf76 : checkPow localTest 9728 7 = true := by
  decide +kernel

private theorem leaf77 : checkPow localTest 9856 7 = true := by
  decide +kernel

private theorem leaf78 : checkPow localTest 9984 7 = true := by
  decide +kernel

private theorem leaf79 : checkPow localTest 10112 7 = true := by
  decide +kernel

private theorem leaf80 : checkPow localTest 10240 7 = true := by
  decide +kernel

private theorem leaf81 : checkPow localTest 10368 7 = true := by
  decide +kernel

private theorem leaf82 : checkPow localTest 10496 7 = true := by
  decide +kernel

private theorem leaf83 : checkPow localTest 10624 7 = true := by
  decide +kernel

private theorem leaf84 : checkPow localTest 10752 7 = true := by
  decide +kernel

private theorem leaf85 : checkPow localTest 10880 7 = true := by
  decide +kernel

private theorem leaf86 : checkPow localTest 11008 7 = true := by
  decide +kernel

private theorem leaf87 : checkPow localTest 11136 7 = true := by
  decide +kernel

private theorem leaf88 : checkPow localTest 11264 7 = true := by
  decide +kernel

private theorem leaf89 : checkPow localTest 11392 7 = true := by
  decide +kernel

private theorem leaf90 : checkPow localTest 11520 7 = true := by
  decide +kernel

private theorem leaf91 : checkPow localTest 11648 7 = true := by
  decide +kernel

private theorem leaf92 : checkPow localTest 11776 7 = true := by
  decide +kernel

private theorem leaf93 : checkPow localTest 11904 7 = true := by
  decide +kernel

private theorem leaf94 : checkPow localTest 12032 7 = true := by
  decide +kernel

private theorem leaf95 : checkPow localTest 12160 7 = true := by
  decide +kernel

private theorem joined8192_8 : checkPow localTest 8192 8 = true :=
  checkPow_join localTest 7 8192 leaf64 leaf65

private theorem joined8448_8 : checkPow localTest 8448 8 = true :=
  checkPow_join localTest 7 8448 leaf66 leaf67

private theorem joined8192_9 : checkPow localTest 8192 9 = true :=
  checkPow_join localTest 8 8192 joined8192_8 joined8448_8

private theorem joined8704_8 : checkPow localTest 8704 8 = true :=
  checkPow_join localTest 7 8704 leaf68 leaf69

private theorem joined8960_8 : checkPow localTest 8960 8 = true :=
  checkPow_join localTest 7 8960 leaf70 leaf71

private theorem joined8704_9 : checkPow localTest 8704 9 = true :=
  checkPow_join localTest 8 8704 joined8704_8 joined8960_8

private theorem joined8192_10 : checkPow localTest 8192 10 = true :=
  checkPow_join localTest 9 8192 joined8192_9 joined8704_9

private theorem joined9216_8 : checkPow localTest 9216 8 = true :=
  checkPow_join localTest 7 9216 leaf72 leaf73

private theorem joined9472_8 : checkPow localTest 9472 8 = true :=
  checkPow_join localTest 7 9472 leaf74 leaf75

private theorem joined9216_9 : checkPow localTest 9216 9 = true :=
  checkPow_join localTest 8 9216 joined9216_8 joined9472_8

private theorem joined9728_8 : checkPow localTest 9728 8 = true :=
  checkPow_join localTest 7 9728 leaf76 leaf77

private theorem joined9984_8 : checkPow localTest 9984 8 = true :=
  checkPow_join localTest 7 9984 leaf78 leaf79

private theorem joined9728_9 : checkPow localTest 9728 9 = true :=
  checkPow_join localTest 8 9728 joined9728_8 joined9984_8

private theorem joined9216_10 : checkPow localTest 9216 10 = true :=
  checkPow_join localTest 9 9216 joined9216_9 joined9728_9

private theorem joined8192_11 : checkPow localTest 8192 11 = true :=
  checkPow_join localTest 10 8192 joined8192_10 joined9216_10

private theorem joined10240_8 : checkPow localTest 10240 8 = true :=
  checkPow_join localTest 7 10240 leaf80 leaf81

private theorem joined10496_8 : checkPow localTest 10496 8 = true :=
  checkPow_join localTest 7 10496 leaf82 leaf83

private theorem joined10240_9 : checkPow localTest 10240 9 = true :=
  checkPow_join localTest 8 10240 joined10240_8 joined10496_8

private theorem joined10752_8 : checkPow localTest 10752 8 = true :=
  checkPow_join localTest 7 10752 leaf84 leaf85

private theorem joined11008_8 : checkPow localTest 11008 8 = true :=
  checkPow_join localTest 7 11008 leaf86 leaf87

private theorem joined10752_9 : checkPow localTest 10752 9 = true :=
  checkPow_join localTest 8 10752 joined10752_8 joined11008_8

private theorem joined10240_10 : checkPow localTest 10240 10 = true :=
  checkPow_join localTest 9 10240 joined10240_9 joined10752_9

private theorem joined11264_8 : checkPow localTest 11264 8 = true :=
  checkPow_join localTest 7 11264 leaf88 leaf89

private theorem joined11520_8 : checkPow localTest 11520 8 = true :=
  checkPow_join localTest 7 11520 leaf90 leaf91

private theorem joined11264_9 : checkPow localTest 11264 9 = true :=
  checkPow_join localTest 8 11264 joined11264_8 joined11520_8

private theorem joined11776_8 : checkPow localTest 11776 8 = true :=
  checkPow_join localTest 7 11776 leaf92 leaf93

private theorem joined12032_8 : checkPow localTest 12032 8 = true :=
  checkPow_join localTest 7 12032 leaf94 leaf95

private theorem joined11776_9 : checkPow localTest 11776 9 = true :=
  checkPow_join localTest 8 11776 joined11776_8 joined12032_8

private theorem joined11264_10 : checkPow localTest 11264 10 = true :=
  checkPow_join localTest 9 11264 joined11264_9 joined11776_9

private theorem joined10240_11 : checkPow localTest 10240 11 = true :=
  checkPow_join localTest 10 10240 joined10240_10 joined11264_10

private theorem joined8192_12 : checkPow localTest 8192 12 = true :=
  checkPow_join localTest 11 8192 joined8192_11 joined10240_11

theorem range2_checked (n : Nat) (hn : 8192 ≤ n) (hm : n < 12288) :
    localTest n = true :=
  checkPow_sound localTest 12 8192 joined8192_12 n hn hm

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne

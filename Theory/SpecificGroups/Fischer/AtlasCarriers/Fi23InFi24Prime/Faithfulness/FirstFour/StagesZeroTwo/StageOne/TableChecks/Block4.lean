module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.Setup

/-!
# Stage-one finite checks on [16384, 20480)

Ordinary kernel reduction checks 128 vertices per leaf. The leaves are joined
without repeating their reductions. At most 32 leaves share a compiler process.
Source: `source/tree.json`, ATLAS F24G1-p306936B0; GLS3 Table 5.3v.
Regenerate with `source/emit_checks.py`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne
open Certificate

private theorem leaf128 : checkPow localTest 16384 7 = true := by
  decide +kernel

private theorem leaf129 : checkPow localTest 16512 7 = true := by
  decide +kernel

private theorem leaf130 : checkPow localTest 16640 7 = true := by
  decide +kernel

private theorem leaf131 : checkPow localTest 16768 7 = true := by
  decide +kernel

private theorem leaf132 : checkPow localTest 16896 7 = true := by
  decide +kernel

private theorem leaf133 : checkPow localTest 17024 7 = true := by
  decide +kernel

private theorem leaf134 : checkPow localTest 17152 7 = true := by
  decide +kernel

private theorem leaf135 : checkPow localTest 17280 7 = true := by
  decide +kernel

private theorem leaf136 : checkPow localTest 17408 7 = true := by
  decide +kernel

private theorem leaf137 : checkPow localTest 17536 7 = true := by
  decide +kernel

private theorem leaf138 : checkPow localTest 17664 7 = true := by
  decide +kernel

private theorem leaf139 : checkPow localTest 17792 7 = true := by
  decide +kernel

private theorem leaf140 : checkPow localTest 17920 7 = true := by
  decide +kernel

private theorem leaf141 : checkPow localTest 18048 7 = true := by
  decide +kernel

private theorem leaf142 : checkPow localTest 18176 7 = true := by
  decide +kernel

private theorem leaf143 : checkPow localTest 18304 7 = true := by
  decide +kernel

private theorem leaf144 : checkPow localTest 18432 7 = true := by
  decide +kernel

private theorem leaf145 : checkPow localTest 18560 7 = true := by
  decide +kernel

private theorem leaf146 : checkPow localTest 18688 7 = true := by
  decide +kernel

private theorem leaf147 : checkPow localTest 18816 7 = true := by
  decide +kernel

private theorem leaf148 : checkPow localTest 18944 7 = true := by
  decide +kernel

private theorem leaf149 : checkPow localTest 19072 7 = true := by
  decide +kernel

private theorem leaf150 : checkPow localTest 19200 7 = true := by
  decide +kernel

private theorem leaf151 : checkPow localTest 19328 7 = true := by
  decide +kernel

private theorem leaf152 : checkPow localTest 19456 7 = true := by
  decide +kernel

private theorem leaf153 : checkPow localTest 19584 7 = true := by
  decide +kernel

private theorem leaf154 : checkPow localTest 19712 7 = true := by
  decide +kernel

private theorem leaf155 : checkPow localTest 19840 7 = true := by
  decide +kernel

private theorem leaf156 : checkPow localTest 19968 7 = true := by
  decide +kernel

private theorem leaf157 : checkPow localTest 20096 7 = true := by
  decide +kernel

private theorem leaf158 : checkPow localTest 20224 7 = true := by
  decide +kernel

private theorem leaf159 : checkPow localTest 20352 7 = true := by
  decide +kernel

private theorem joined16384_8 : checkPow localTest 16384 8 = true :=
  checkPow_join localTest 7 16384 leaf128 leaf129

private theorem joined16640_8 : checkPow localTest 16640 8 = true :=
  checkPow_join localTest 7 16640 leaf130 leaf131

private theorem joined16384_9 : checkPow localTest 16384 9 = true :=
  checkPow_join localTest 8 16384 joined16384_8 joined16640_8

private theorem joined16896_8 : checkPow localTest 16896 8 = true :=
  checkPow_join localTest 7 16896 leaf132 leaf133

private theorem joined17152_8 : checkPow localTest 17152 8 = true :=
  checkPow_join localTest 7 17152 leaf134 leaf135

private theorem joined16896_9 : checkPow localTest 16896 9 = true :=
  checkPow_join localTest 8 16896 joined16896_8 joined17152_8

private theorem joined16384_10 : checkPow localTest 16384 10 = true :=
  checkPow_join localTest 9 16384 joined16384_9 joined16896_9

private theorem joined17408_8 : checkPow localTest 17408 8 = true :=
  checkPow_join localTest 7 17408 leaf136 leaf137

private theorem joined17664_8 : checkPow localTest 17664 8 = true :=
  checkPow_join localTest 7 17664 leaf138 leaf139

private theorem joined17408_9 : checkPow localTest 17408 9 = true :=
  checkPow_join localTest 8 17408 joined17408_8 joined17664_8

private theorem joined17920_8 : checkPow localTest 17920 8 = true :=
  checkPow_join localTest 7 17920 leaf140 leaf141

private theorem joined18176_8 : checkPow localTest 18176 8 = true :=
  checkPow_join localTest 7 18176 leaf142 leaf143

private theorem joined17920_9 : checkPow localTest 17920 9 = true :=
  checkPow_join localTest 8 17920 joined17920_8 joined18176_8

private theorem joined17408_10 : checkPow localTest 17408 10 = true :=
  checkPow_join localTest 9 17408 joined17408_9 joined17920_9

private theorem joined16384_11 : checkPow localTest 16384 11 = true :=
  checkPow_join localTest 10 16384 joined16384_10 joined17408_10

private theorem joined18432_8 : checkPow localTest 18432 8 = true :=
  checkPow_join localTest 7 18432 leaf144 leaf145

private theorem joined18688_8 : checkPow localTest 18688 8 = true :=
  checkPow_join localTest 7 18688 leaf146 leaf147

private theorem joined18432_9 : checkPow localTest 18432 9 = true :=
  checkPow_join localTest 8 18432 joined18432_8 joined18688_8

private theorem joined18944_8 : checkPow localTest 18944 8 = true :=
  checkPow_join localTest 7 18944 leaf148 leaf149

private theorem joined19200_8 : checkPow localTest 19200 8 = true :=
  checkPow_join localTest 7 19200 leaf150 leaf151

private theorem joined18944_9 : checkPow localTest 18944 9 = true :=
  checkPow_join localTest 8 18944 joined18944_8 joined19200_8

private theorem joined18432_10 : checkPow localTest 18432 10 = true :=
  checkPow_join localTest 9 18432 joined18432_9 joined18944_9

private theorem joined19456_8 : checkPow localTest 19456 8 = true :=
  checkPow_join localTest 7 19456 leaf152 leaf153

private theorem joined19712_8 : checkPow localTest 19712 8 = true :=
  checkPow_join localTest 7 19712 leaf154 leaf155

private theorem joined19456_9 : checkPow localTest 19456 9 = true :=
  checkPow_join localTest 8 19456 joined19456_8 joined19712_8

private theorem joined19968_8 : checkPow localTest 19968 8 = true :=
  checkPow_join localTest 7 19968 leaf156 leaf157

private theorem joined20224_8 : checkPow localTest 20224 8 = true :=
  checkPow_join localTest 7 20224 leaf158 leaf159

private theorem joined19968_9 : checkPow localTest 19968 9 = true :=
  checkPow_join localTest 8 19968 joined19968_8 joined20224_8

private theorem joined19456_10 : checkPow localTest 19456 10 = true :=
  checkPow_join localTest 9 19456 joined19456_9 joined19968_9

private theorem joined18432_11 : checkPow localTest 18432 11 = true :=
  checkPow_join localTest 10 18432 joined18432_10 joined19456_10

private theorem joined16384_12 : checkPow localTest 16384 12 = true :=
  checkPow_join localTest 11 16384 joined16384_11 joined18432_11

theorem range4_checked (n : Nat) (hn : 16384 ≤ n) (hm : n < 20480) :
    localTest n = true :=
  checkPow_sound localTest 12 16384 joined16384_12 n hn hm

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne

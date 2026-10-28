module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.Setup

/-!
# Stage-one finite checks on [24576, 28160)

Ordinary kernel reduction checks 128 vertices per leaf. The leaves are joined
without repeating their reductions. At most 32 leaves share a compiler process.
Source: `source/tree.json`, ATLAS F24G1-p306936B0; GLS3 Table 5.3v.
Regenerate with `source/emit_checks.py`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne
open Certificate

private theorem leaf192 : checkPow localTest 24576 7 = true := by
  decide +kernel

private theorem leaf193 : checkPow localTest 24704 7 = true := by
  decide +kernel

private theorem leaf194 : checkPow localTest 24832 7 = true := by
  decide +kernel

private theorem leaf195 : checkPow localTest 24960 7 = true := by
  decide +kernel

private theorem leaf196 : checkPow localTest 25088 7 = true := by
  decide +kernel

private theorem leaf197 : checkPow localTest 25216 7 = true := by
  decide +kernel

private theorem leaf198 : checkPow localTest 25344 7 = true := by
  decide +kernel

private theorem leaf199 : checkPow localTest 25472 7 = true := by
  decide +kernel

private theorem leaf200 : checkPow localTest 25600 7 = true := by
  decide +kernel

private theorem leaf201 : checkPow localTest 25728 7 = true := by
  decide +kernel

private theorem leaf202 : checkPow localTest 25856 7 = true := by
  decide +kernel

private theorem leaf203 : checkPow localTest 25984 7 = true := by
  decide +kernel

private theorem leaf204 : checkPow localTest 26112 7 = true := by
  decide +kernel

private theorem leaf205 : checkPow localTest 26240 7 = true := by
  decide +kernel

private theorem leaf206 : checkPow localTest 26368 7 = true := by
  decide +kernel

private theorem leaf207 : checkPow localTest 26496 7 = true := by
  decide +kernel

private theorem leaf208 : checkPow localTest 26624 7 = true := by
  decide +kernel

private theorem leaf209 : checkPow localTest 26752 7 = true := by
  decide +kernel

private theorem leaf210 : checkPow localTest 26880 7 = true := by
  decide +kernel

private theorem leaf211 : checkPow localTest 27008 7 = true := by
  decide +kernel

private theorem leaf212 : checkPow localTest 27136 7 = true := by
  decide +kernel

private theorem leaf213 : checkPow localTest 27264 7 = true := by
  decide +kernel

private theorem leaf214 : checkPow localTest 27392 7 = true := by
  decide +kernel

private theorem leaf215 : checkPow localTest 27520 7 = true := by
  decide +kernel

private theorem leaf216 : checkPow localTest 27648 7 = true := by
  decide +kernel

private theorem leaf217 : checkPow localTest 27776 7 = true := by
  decide +kernel

private theorem leaf218 : checkPow localTest 27904 7 = true := by
  decide +kernel

private theorem leaf219 : checkPow localTest 28032 7 = true := by
  decide +kernel

private theorem joined24576_8 : checkPow localTest 24576 8 = true :=
  checkPow_join localTest 7 24576 leaf192 leaf193

private theorem joined24832_8 : checkPow localTest 24832 8 = true :=
  checkPow_join localTest 7 24832 leaf194 leaf195

private theorem joined24576_9 : checkPow localTest 24576 9 = true :=
  checkPow_join localTest 8 24576 joined24576_8 joined24832_8

private theorem joined25088_8 : checkPow localTest 25088 8 = true :=
  checkPow_join localTest 7 25088 leaf196 leaf197

private theorem joined25344_8 : checkPow localTest 25344 8 = true :=
  checkPow_join localTest 7 25344 leaf198 leaf199

private theorem joined25088_9 : checkPow localTest 25088 9 = true :=
  checkPow_join localTest 8 25088 joined25088_8 joined25344_8

private theorem joined24576_10 : checkPow localTest 24576 10 = true :=
  checkPow_join localTest 9 24576 joined24576_9 joined25088_9

private theorem joined25600_8 : checkPow localTest 25600 8 = true :=
  checkPow_join localTest 7 25600 leaf200 leaf201

private theorem joined25856_8 : checkPow localTest 25856 8 = true :=
  checkPow_join localTest 7 25856 leaf202 leaf203

private theorem joined25600_9 : checkPow localTest 25600 9 = true :=
  checkPow_join localTest 8 25600 joined25600_8 joined25856_8

private theorem joined26112_8 : checkPow localTest 26112 8 = true :=
  checkPow_join localTest 7 26112 leaf204 leaf205

private theorem joined26368_8 : checkPow localTest 26368 8 = true :=
  checkPow_join localTest 7 26368 leaf206 leaf207

private theorem joined26112_9 : checkPow localTest 26112 9 = true :=
  checkPow_join localTest 8 26112 joined26112_8 joined26368_8

private theorem joined25600_10 : checkPow localTest 25600 10 = true :=
  checkPow_join localTest 9 25600 joined25600_9 joined26112_9

private theorem joined24576_11 : checkPow localTest 24576 11 = true :=
  checkPow_join localTest 10 24576 joined24576_10 joined25600_10

private theorem joined26624_8 : checkPow localTest 26624 8 = true :=
  checkPow_join localTest 7 26624 leaf208 leaf209

private theorem joined26880_8 : checkPow localTest 26880 8 = true :=
  checkPow_join localTest 7 26880 leaf210 leaf211

private theorem joined26624_9 : checkPow localTest 26624 9 = true :=
  checkPow_join localTest 8 26624 joined26624_8 joined26880_8

private theorem joined27136_8 : checkPow localTest 27136 8 = true :=
  checkPow_join localTest 7 27136 leaf212 leaf213

private theorem joined27392_8 : checkPow localTest 27392 8 = true :=
  checkPow_join localTest 7 27392 leaf214 leaf215

private theorem joined27136_9 : checkPow localTest 27136 9 = true :=
  checkPow_join localTest 8 27136 joined27136_8 joined27392_8

private theorem joined26624_10 : checkPow localTest 26624 10 = true :=
  checkPow_join localTest 9 26624 joined26624_9 joined27136_9

private theorem joined27648_8 : checkPow localTest 27648 8 = true :=
  checkPow_join localTest 7 27648 leaf216 leaf217

private theorem joined27904_8 : checkPow localTest 27904 8 = true :=
  checkPow_join localTest 7 27904 leaf218 leaf219

private theorem joined27648_9 : checkPow localTest 27648 9 = true :=
  checkPow_join localTest 8 27648 joined27648_8 joined27904_8

theorem range6_checked (n : Nat) (hn : 24576 ≤ n) (hm : n < 28160) :
    localTest n = true := by
  by_cases h₀ : n < 26624
  · exact checkPow_sound localTest 11 24576 joined24576_11 n hn h₀
  by_cases h₁ : n < 27648
  · exact checkPow_sound localTest 10 26624 joined26624_10 n (by omega) h₁
  · exact checkPow_sound localTest 9 27648 joined27648_9 n (by omega) hm

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne

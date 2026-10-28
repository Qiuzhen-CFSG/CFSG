module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.Setup

/-!
# Stage-one finite checks on [20480, 24576)

Ordinary kernel reduction checks 128 vertices per leaf. The leaves are joined
without repeating their reductions. At most 32 leaves share a compiler process.
Source: `source/tree.json`, ATLAS F24G1-p306936B0; GLS3 Table 5.3v.
Regenerate with `source/emit_checks.py`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne
open Certificate

private theorem leaf160 : checkPow localTest 20480 7 = true := by
  decide +kernel

private theorem leaf161 : checkPow localTest 20608 7 = true := by
  decide +kernel

private theorem leaf162 : checkPow localTest 20736 7 = true := by
  decide +kernel

private theorem leaf163 : checkPow localTest 20864 7 = true := by
  decide +kernel

private theorem leaf164 : checkPow localTest 20992 7 = true := by
  decide +kernel

private theorem leaf165 : checkPow localTest 21120 7 = true := by
  decide +kernel

private theorem leaf166 : checkPow localTest 21248 7 = true := by
  decide +kernel

private theorem leaf167 : checkPow localTest 21376 7 = true := by
  decide +kernel

private theorem leaf168 : checkPow localTest 21504 7 = true := by
  decide +kernel

private theorem leaf169 : checkPow localTest 21632 7 = true := by
  decide +kernel

private theorem leaf170 : checkPow localTest 21760 7 = true := by
  decide +kernel

private theorem leaf171 : checkPow localTest 21888 7 = true := by
  decide +kernel

private theorem leaf172 : checkPow localTest 22016 7 = true := by
  decide +kernel

private theorem leaf173 : checkPow localTest 22144 7 = true := by
  decide +kernel

private theorem leaf174 : checkPow localTest 22272 7 = true := by
  decide +kernel

private theorem leaf175 : checkPow localTest 22400 7 = true := by
  decide +kernel

private theorem leaf176 : checkPow localTest 22528 7 = true := by
  decide +kernel

private theorem leaf177 : checkPow localTest 22656 7 = true := by
  decide +kernel

private theorem leaf178 : checkPow localTest 22784 7 = true := by
  decide +kernel

private theorem leaf179 : checkPow localTest 22912 7 = true := by
  decide +kernel

private theorem leaf180 : checkPow localTest 23040 7 = true := by
  decide +kernel

private theorem leaf181 : checkPow localTest 23168 7 = true := by
  decide +kernel

private theorem leaf182 : checkPow localTest 23296 7 = true := by
  decide +kernel

private theorem leaf183 : checkPow localTest 23424 7 = true := by
  decide +kernel

private theorem leaf184 : checkPow localTest 23552 7 = true := by
  decide +kernel

private theorem leaf185 : checkPow localTest 23680 7 = true := by
  decide +kernel

private theorem leaf186 : checkPow localTest 23808 7 = true := by
  decide +kernel

private theorem leaf187 : checkPow localTest 23936 7 = true := by
  decide +kernel

private theorem leaf188 : checkPow localTest 24064 7 = true := by
  decide +kernel

private theorem leaf189 : checkPow localTest 24192 7 = true := by
  decide +kernel

private theorem leaf190 : checkPow localTest 24320 7 = true := by
  decide +kernel

private theorem leaf191 : checkPow localTest 24448 7 = true := by
  decide +kernel

private theorem joined20480_8 : checkPow localTest 20480 8 = true :=
  checkPow_join localTest 7 20480 leaf160 leaf161

private theorem joined20736_8 : checkPow localTest 20736 8 = true :=
  checkPow_join localTest 7 20736 leaf162 leaf163

private theorem joined20480_9 : checkPow localTest 20480 9 = true :=
  checkPow_join localTest 8 20480 joined20480_8 joined20736_8

private theorem joined20992_8 : checkPow localTest 20992 8 = true :=
  checkPow_join localTest 7 20992 leaf164 leaf165

private theorem joined21248_8 : checkPow localTest 21248 8 = true :=
  checkPow_join localTest 7 21248 leaf166 leaf167

private theorem joined20992_9 : checkPow localTest 20992 9 = true :=
  checkPow_join localTest 8 20992 joined20992_8 joined21248_8

private theorem joined20480_10 : checkPow localTest 20480 10 = true :=
  checkPow_join localTest 9 20480 joined20480_9 joined20992_9

private theorem joined21504_8 : checkPow localTest 21504 8 = true :=
  checkPow_join localTest 7 21504 leaf168 leaf169

private theorem joined21760_8 : checkPow localTest 21760 8 = true :=
  checkPow_join localTest 7 21760 leaf170 leaf171

private theorem joined21504_9 : checkPow localTest 21504 9 = true :=
  checkPow_join localTest 8 21504 joined21504_8 joined21760_8

private theorem joined22016_8 : checkPow localTest 22016 8 = true :=
  checkPow_join localTest 7 22016 leaf172 leaf173

private theorem joined22272_8 : checkPow localTest 22272 8 = true :=
  checkPow_join localTest 7 22272 leaf174 leaf175

private theorem joined22016_9 : checkPow localTest 22016 9 = true :=
  checkPow_join localTest 8 22016 joined22016_8 joined22272_8

private theorem joined21504_10 : checkPow localTest 21504 10 = true :=
  checkPow_join localTest 9 21504 joined21504_9 joined22016_9

private theorem joined20480_11 : checkPow localTest 20480 11 = true :=
  checkPow_join localTest 10 20480 joined20480_10 joined21504_10

private theorem joined22528_8 : checkPow localTest 22528 8 = true :=
  checkPow_join localTest 7 22528 leaf176 leaf177

private theorem joined22784_8 : checkPow localTest 22784 8 = true :=
  checkPow_join localTest 7 22784 leaf178 leaf179

private theorem joined22528_9 : checkPow localTest 22528 9 = true :=
  checkPow_join localTest 8 22528 joined22528_8 joined22784_8

private theorem joined23040_8 : checkPow localTest 23040 8 = true :=
  checkPow_join localTest 7 23040 leaf180 leaf181

private theorem joined23296_8 : checkPow localTest 23296 8 = true :=
  checkPow_join localTest 7 23296 leaf182 leaf183

private theorem joined23040_9 : checkPow localTest 23040 9 = true :=
  checkPow_join localTest 8 23040 joined23040_8 joined23296_8

private theorem joined22528_10 : checkPow localTest 22528 10 = true :=
  checkPow_join localTest 9 22528 joined22528_9 joined23040_9

private theorem joined23552_8 : checkPow localTest 23552 8 = true :=
  checkPow_join localTest 7 23552 leaf184 leaf185

private theorem joined23808_8 : checkPow localTest 23808 8 = true :=
  checkPow_join localTest 7 23808 leaf186 leaf187

private theorem joined23552_9 : checkPow localTest 23552 9 = true :=
  checkPow_join localTest 8 23552 joined23552_8 joined23808_8

private theorem joined24064_8 : checkPow localTest 24064 8 = true :=
  checkPow_join localTest 7 24064 leaf188 leaf189

private theorem joined24320_8 : checkPow localTest 24320 8 = true :=
  checkPow_join localTest 7 24320 leaf190 leaf191

private theorem joined24064_9 : checkPow localTest 24064 9 = true :=
  checkPow_join localTest 8 24064 joined24064_8 joined24320_8

private theorem joined23552_10 : checkPow localTest 23552 10 = true :=
  checkPow_join localTest 9 23552 joined23552_9 joined24064_9

private theorem joined22528_11 : checkPow localTest 22528 11 = true :=
  checkPow_join localTest 10 22528 joined22528_10 joined23552_10

private theorem joined20480_12 : checkPow localTest 20480 12 = true :=
  checkPow_join localTest 11 20480 joined20480_11 joined22528_11

theorem range5_checked (n : Nat) (hn : 20480 ≤ n) (hm : n < 24576) :
    localTest n = true :=
  checkPow_sound localTest 12 20480 joined20480_12 n hn hm

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne

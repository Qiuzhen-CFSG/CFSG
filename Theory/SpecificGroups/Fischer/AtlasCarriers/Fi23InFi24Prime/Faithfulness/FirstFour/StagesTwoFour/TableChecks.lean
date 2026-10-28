module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Setup

/-!
# Kernel checks of the finite coset trees

These checks prove the two inverse table laws, isolation of the base label,
and the literal word equations for every tree edge. They evaluate only the
small table entries, never a long ambient permutation word. The remaining
`InverseAction` and `NonTreeEdges` premises are not assumed by these checks.
Source: ATLAS F24G1-p306936B0, retained `source/trees.json`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour
open Certificate

private theorem block0_0 : checkPow (localTest 0) 0 7 = true := by
  decide +kernel

private theorem block0_1 : checkPow (localTest 0) 128 7 = true := by
  decide +kernel

private theorem block0_2 : checkPow (localTest 0) 256 7 = true := by
  decide +kernel

private theorem block0_3 : checkPow (localTest 0) 384 7 = true := by
  decide +kernel

private theorem block0_4 : checkPow (localTest 0) 512 7 = true := by
  decide +kernel

private theorem block0_5 : checkPow (localTest 0) 640 7 = true := by
  decide +kernel

private theorem block0_6 : checkPow (localTest 0) 768 7 = true := by
  decide +kernel

private theorem block0_7 : checkPow (localTest 0) 896 7 = true := by
  decide +kernel

private theorem block0_8 : checkPow (localTest 0) 1024 7 = true := by
  decide +kernel

private theorem block0_9 : checkPow (localTest 0) 1152 7 = true := by
  decide +kernel

private theorem block0_10 : checkPow (localTest 0) 1280 7 = true := by
  decide +kernel

private theorem block0_11 : checkPow (localTest 0) 1408 7 = true := by
  decide +kernel

private theorem block0_12 : checkPow (localTest 0) 1536 7 = true := by
  decide +kernel

private theorem block0_13 : checkPow (localTest 0) 1664 7 = true := by
  decide +kernel

private theorem block0_14 : checkPow (localTest 0) 1792 7 = true := by
  decide +kernel

private theorem block0_15 : checkPow (localTest 0) 1920 7 = true := by
  decide +kernel

private theorem block0_16 : checkPow (localTest 0) 2048 7 = true := by
  decide +kernel

private theorem block0_17 : checkPow (localTest 0) 2176 7 = true := by
  decide +kernel

private theorem block0_18 : checkPow (localTest 0) 2304 7 = true := by
  decide +kernel

private theorem block0_19 : checkPow (localTest 0) 2432 7 = true := by
  decide +kernel

private theorem block0_20 : checkPow (localTest 0) 2560 7 = true := by
  decide +kernel

private theorem block0_21 : checkPow (localTest 0) 2688 7 = true := by
  decide +kernel

private theorem block0_22 : checkPow (localTest 0) 2816 7 = true := by
  decide +kernel

private theorem block0_23 : checkPow (localTest 0) 2944 7 = true := by
  decide +kernel

private theorem block0_24 : checkPow (localTest 0) 3072 7 = true := by
  decide +kernel

private theorem block0_25 : checkPow (localTest 0) 3200 7 = true := by
  decide +kernel

private theorem block0_26 : checkPow (localTest 0) 3328 7 = true := by
  decide +kernel

private theorem block0_27 : checkPow (localTest 0) 3456 7 = true := by
  decide +kernel

private theorem block0_28 : checkPow (localTest 0) 3584 7 = true := by
  decide +kernel

private theorem block0_29 : checkPow (localTest 0) 3712 7 = true := by
  decide +kernel

private theorem block0_30 : checkPow (localTest 0) 3840 7 = true := by
  decide +kernel

private theorem block0_31 : checkPow (localTest 0) 3968 7 = true := by
  decide +kernel

private theorem checked0 : checkPow (localTest 0) 0 12 = true :=
  (checkPow_join (localTest 0) 11 0 (checkPow_join (localTest 0) 10 0 (checkPow_join (localTest 0) 9 0 (checkPow_join (localTest 0) 8 0 (checkPow_join (localTest 0) 7 0 block0_0 block0_1) (checkPow_join (localTest 0) 7 256 block0_2 block0_3)) (checkPow_join (localTest 0) 8 512 (checkPow_join (localTest 0) 7 512 block0_4 block0_5) (checkPow_join (localTest 0) 7 768 block0_6 block0_7))) (checkPow_join (localTest 0) 9 1024 (checkPow_join (localTest 0) 8 1024 (checkPow_join (localTest 0) 7 1024 block0_8 block0_9) (checkPow_join (localTest 0) 7 1280 block0_10 block0_11)) (checkPow_join (localTest 0) 8 1536 (checkPow_join (localTest 0) 7 1536 block0_12 block0_13) (checkPow_join (localTest 0) 7 1792 block0_14 block0_15)))) (checkPow_join (localTest 0) 10 2048 (checkPow_join (localTest 0) 9 2048 (checkPow_join (localTest 0) 8 2048 (checkPow_join (localTest 0) 7 2048 block0_16 block0_17) (checkPow_join (localTest 0) 7 2304 block0_18 block0_19)) (checkPow_join (localTest 0) 8 2560 (checkPow_join (localTest 0) 7 2560 block0_20 block0_21) (checkPow_join (localTest 0) 7 2816 block0_22 block0_23))) (checkPow_join (localTest 0) 9 3072 (checkPow_join (localTest 0) 8 3072 (checkPow_join (localTest 0) 7 3072 block0_24 block0_25) (checkPow_join (localTest 0) 7 3328 block0_26 block0_27)) (checkPow_join (localTest 0) 8 3584 (checkPow_join (localTest 0) 7 3584 block0_28 block0_29) (checkPow_join (localTest 0) 7 3840 block0_30 block0_31)))))

private theorem block1_0 : checkPow (localTest 1) 0 7 = true := by
  decide +kernel

private theorem block1_1 : checkPow (localTest 1) 128 7 = true := by
  decide +kernel

private theorem block1_2 : checkPow (localTest 1) 256 7 = true := by
  decide +kernel

private theorem block1_3 : checkPow (localTest 1) 384 7 = true := by
  decide +kernel

private theorem block1_4 : checkPow (localTest 1) 512 7 = true := by
  decide +kernel

private theorem block1_5 : checkPow (localTest 1) 640 7 = true := by
  decide +kernel

private theorem block1_6 : checkPow (localTest 1) 768 7 = true := by
  decide +kernel

private theorem block1_7 : checkPow (localTest 1) 896 7 = true := by
  decide +kernel

private theorem checked1 : checkPow (localTest 1) 0 10 = true :=
  (checkPow_join (localTest 1) 9 0 (checkPow_join (localTest 1) 8 0 (checkPow_join (localTest 1) 7 0 block1_0 block1_1) (checkPow_join (localTest 1) 7 256 block1_2 block1_3)) (checkPow_join (localTest 1) 8 512 (checkPow_join (localTest 1) 7 512 block1_4 block1_5) (checkPow_join (localTest 1) 7 768 block1_6 block1_7)))

theorem table_facts (i : Fin 2) (j : Fin (size i)) :
    (∀ a : Fin 2, prev i a (next i a j) = j ∧ next i a (prev i a j) = j) ∧
    (label i j = label i (root i) → j = root i) ∧
    (j ≠ root i → repWord i j = repWord i (parent i j) ++ [letter i j] ∧
      next i (letter i j) (parent i j) = j ∧ (parent i j).val < j.val) := by
  have hc : checkPow (localTest i) 0 (if i = 0 then 12 else 10) = true := by
    fin_cases i
    · exact checked0
    · exact checked1
  have hb : size i ≤ 2 ^ (if i = 0 then 12 else 10) := by fin_cases i <;> decide
  have h := checkPow_sound (localTest i) _ 0 hc j.val (Nat.zero_le _)
    (by simpa only [Nat.zero_add] using lt_of_lt_of_le j.isLt hb)
  simpa only [localTest, Nat.mod_eq_of_lt j.isLt, Fin.eta, decide_eq_true_eq] using h

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour

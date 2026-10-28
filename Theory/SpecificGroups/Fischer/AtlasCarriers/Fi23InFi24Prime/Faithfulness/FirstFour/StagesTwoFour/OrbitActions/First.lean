module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.OrbitActions.Evaluation

/-!
# Checked common-preimage equations for the first orbit

Each check compares short products using already certified actions. These are
literal point comparisons, not assumptions about orders or stabilizers.
Source: ATLAS F24G1-p306936B0, GLS3 Table 5.3v, and the retained orbit trees.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.OrbitActions
open Certificate

-- Keep the bounded numerical reductions sequential.
set_option Elab.async false

private theorem check0_0 : checkPow (firstTest 0) 0 7 = true := by
  decide +kernel

private theorem check0_1 : checkPow (firstTest 0) 128 7 = true := by
  decide +kernel

private theorem check0_2 : checkPow (firstTest 0) 256 7 = true := by
  decide +kernel

private theorem check0_3 : checkPow (firstTest 0) 384 7 = true := by
  decide +kernel

private theorem check0_4 : checkPow (firstTest 0) 512 7 = true := by
  decide +kernel

private theorem check0_5 : checkPow (firstTest 0) 640 7 = true := by
  decide +kernel

private theorem check0_6 : checkPow (firstTest 0) 768 7 = true := by
  decide +kernel

private theorem check0_7 : checkPow (firstTest 0) 896 7 = true := by
  decide +kernel

private theorem check0_8 : checkPow (firstTest 0) 1024 7 = true := by
  decide +kernel

private theorem check0_9 : checkPow (firstTest 0) 1152 7 = true := by
  decide +kernel

private theorem check0_10 : checkPow (firstTest 0) 1280 7 = true := by
  decide +kernel

private theorem check0_11 : checkPow (firstTest 0) 1408 7 = true := by
  decide +kernel

private theorem check0_12 : checkPow (firstTest 0) 1536 7 = true := by
  decide +kernel

private theorem check0_13 : checkPow (firstTest 0) 1664 7 = true := by
  decide +kernel

private theorem check0_14 : checkPow (firstTest 0) 1792 7 = true := by
  decide +kernel

private theorem check0_15 : checkPow (firstTest 0) 1920 7 = true := by
  decide +kernel

private theorem check0_16 : checkPow (firstTest 0) 2048 7 = true := by
  decide +kernel

private theorem check0_17 : checkPow (firstTest 0) 2176 7 = true := by
  decide +kernel

private theorem check0_18 : checkPow (firstTest 0) 2304 7 = true := by
  decide +kernel

private theorem check0_19 : checkPow (firstTest 0) 2432 7 = true := by
  decide +kernel

private theorem check0_20 : checkPow (firstTest 0) 2560 7 = true := by
  decide +kernel

private theorem check0_21 : checkPow (firstTest 0) 2688 7 = true := by
  decide +kernel

private theorem check0_22 : checkPow (firstTest 0) 2816 7 = true := by
  decide +kernel

private theorem check0_23 : checkPow (firstTest 0) 2944 7 = true := by
  decide +kernel

private theorem check0_24 : checkPow (firstTest 0) 3072 7 = true := by
  decide +kernel

private theorem check0_25 : checkPow (firstTest 0) 3200 7 = true := by
  decide +kernel

private theorem check0_26 : checkPow (firstTest 0) 3328 7 = true := by
  decide +kernel

private theorem check0_27 : checkPow (firstTest 0) 3456 7 = true := by
  decide +kernel

private theorem check0_28 : checkPow (firstTest 0) 3584 7 = true := by
  decide +kernel

private theorem check0_29 : checkPow (firstTest 0) 3712 7 = true := by
  decide +kernel

private theorem check0_30 : checkPow (firstTest 0) 3840 7 = true := by
  decide +kernel

private theorem check0_31 : checkPow (firstTest 0) 3968 7 = true := by
  decide +kernel

private theorem checked0 : checkPow (firstTest 0) 0 12 = true :=
  (checkPow_join (firstTest 0) 11 0 (checkPow_join (firstTest 0) 10 0 (checkPow_join (firstTest 0) 9 0 (checkPow_join (firstTest 0) 8 0 (checkPow_join (firstTest 0) 7 0 check0_0 check0_1) (checkPow_join (firstTest 0) 7 256 check0_2 check0_3)) (checkPow_join (firstTest 0) 8 512 (checkPow_join (firstTest 0) 7 512 check0_4 check0_5) (checkPow_join (firstTest 0) 7 768 check0_6 check0_7))) (checkPow_join (firstTest 0) 9 1024 (checkPow_join (firstTest 0) 8 1024 (checkPow_join (firstTest 0) 7 1024 check0_8 check0_9) (checkPow_join (firstTest 0) 7 1280 check0_10 check0_11)) (checkPow_join (firstTest 0) 8 1536 (checkPow_join (firstTest 0) 7 1536 check0_12 check0_13) (checkPow_join (firstTest 0) 7 1792 check0_14 check0_15)))) (checkPow_join (firstTest 0) 10 2048 (checkPow_join (firstTest 0) 9 2048 (checkPow_join (firstTest 0) 8 2048 (checkPow_join (firstTest 0) 7 2048 check0_16 check0_17) (checkPow_join (firstTest 0) 7 2304 check0_18 check0_19)) (checkPow_join (firstTest 0) 8 2560 (checkPow_join (firstTest 0) 7 2560 check0_20 check0_21) (checkPow_join (firstTest 0) 7 2816 check0_22 check0_23))) (checkPow_join (firstTest 0) 9 3072 (checkPow_join (firstTest 0) 8 3072 (checkPow_join (firstTest 0) 7 3072 check0_24 check0_25) (checkPow_join (firstTest 0) 7 3328 check0_26 check0_27)) (checkPow_join (firstTest 0) 8 3584 (checkPow_join (firstTest 0) 7 3584 check0_28 check0_29) (checkPow_join (firstTest 0) 7 3840 check0_30 check0_31)))))

private theorem check1_0 : checkPow (firstTest 1) 0 7 = true := by
  decide +kernel

private theorem check1_1 : checkPow (firstTest 1) 128 7 = true := by
  decide +kernel

private theorem check1_2 : checkPow (firstTest 1) 256 7 = true := by
  decide +kernel

private theorem check1_3 : checkPow (firstTest 1) 384 7 = true := by
  decide +kernel

private theorem check1_4 : checkPow (firstTest 1) 512 7 = true := by
  decide +kernel

private theorem check1_5 : checkPow (firstTest 1) 640 7 = true := by
  decide +kernel

private theorem check1_6 : checkPow (firstTest 1) 768 7 = true := by
  decide +kernel

private theorem check1_7 : checkPow (firstTest 1) 896 7 = true := by
  decide +kernel

private theorem check1_8 : checkPow (firstTest 1) 1024 7 = true := by
  decide +kernel

private theorem check1_9 : checkPow (firstTest 1) 1152 7 = true := by
  decide +kernel

private theorem check1_10 : checkPow (firstTest 1) 1280 7 = true := by
  decide +kernel

private theorem check1_11 : checkPow (firstTest 1) 1408 7 = true := by
  decide +kernel

private theorem check1_12 : checkPow (firstTest 1) 1536 7 = true := by
  decide +kernel

private theorem check1_13 : checkPow (firstTest 1) 1664 7 = true := by
  decide +kernel

private theorem check1_14 : checkPow (firstTest 1) 1792 7 = true := by
  decide +kernel

private theorem check1_15 : checkPow (firstTest 1) 1920 7 = true := by
  decide +kernel

private theorem check1_16 : checkPow (firstTest 1) 2048 7 = true := by
  decide +kernel

private theorem check1_17 : checkPow (firstTest 1) 2176 7 = true := by
  decide +kernel

private theorem check1_18 : checkPow (firstTest 1) 2304 7 = true := by
  decide +kernel

private theorem check1_19 : checkPow (firstTest 1) 2432 7 = true := by
  decide +kernel

private theorem check1_20 : checkPow (firstTest 1) 2560 7 = true := by
  decide +kernel

private theorem check1_21 : checkPow (firstTest 1) 2688 7 = true := by
  decide +kernel

private theorem check1_22 : checkPow (firstTest 1) 2816 7 = true := by
  decide +kernel

private theorem check1_23 : checkPow (firstTest 1) 2944 7 = true := by
  decide +kernel

private theorem check1_24 : checkPow (firstTest 1) 3072 7 = true := by
  decide +kernel

private theorem check1_25 : checkPow (firstTest 1) 3200 7 = true := by
  decide +kernel

private theorem check1_26 : checkPow (firstTest 1) 3328 7 = true := by
  decide +kernel

private theorem check1_27 : checkPow (firstTest 1) 3456 7 = true := by
  decide +kernel

private theorem check1_28 : checkPow (firstTest 1) 3584 7 = true := by
  decide +kernel

private theorem check1_29 : checkPow (firstTest 1) 3712 7 = true := by
  decide +kernel

private theorem check1_30 : checkPow (firstTest 1) 3840 7 = true := by
  decide +kernel

private theorem check1_31 : checkPow (firstTest 1) 3968 7 = true := by
  decide +kernel

private theorem checked1 : checkPow (firstTest 1) 0 12 = true :=
  (checkPow_join (firstTest 1) 11 0 (checkPow_join (firstTest 1) 10 0 (checkPow_join (firstTest 1) 9 0 (checkPow_join (firstTest 1) 8 0 (checkPow_join (firstTest 1) 7 0 check1_0 check1_1) (checkPow_join (firstTest 1) 7 256 check1_2 check1_3)) (checkPow_join (firstTest 1) 8 512 (checkPow_join (firstTest 1) 7 512 check1_4 check1_5) (checkPow_join (firstTest 1) 7 768 check1_6 check1_7))) (checkPow_join (firstTest 1) 9 1024 (checkPow_join (firstTest 1) 8 1024 (checkPow_join (firstTest 1) 7 1024 check1_8 check1_9) (checkPow_join (firstTest 1) 7 1280 check1_10 check1_11)) (checkPow_join (firstTest 1) 8 1536 (checkPow_join (firstTest 1) 7 1536 check1_12 check1_13) (checkPow_join (firstTest 1) 7 1792 check1_14 check1_15)))) (checkPow_join (firstTest 1) 10 2048 (checkPow_join (firstTest 1) 9 2048 (checkPow_join (firstTest 1) 8 2048 (checkPow_join (firstTest 1) 7 2048 check1_16 check1_17) (checkPow_join (firstTest 1) 7 2304 check1_18 check1_19)) (checkPow_join (firstTest 1) 8 2560 (checkPow_join (firstTest 1) 7 2560 check1_20 check1_21) (checkPow_join (firstTest 1) 7 2816 check1_22 check1_23))) (checkPow_join (firstTest 1) 9 3072 (checkPow_join (firstTest 1) 8 3072 (checkPow_join (firstTest 1) 7 3072 check1_24 check1_25) (checkPow_join (firstTest 1) 7 3328 check1_26 check1_27)) (checkPow_join (firstTest 1) 8 3584 (checkPow_join (firstTest 1) 7 3584 check1_28 check1_29) (checkPow_join (firstTest 1) 7 3840 check1_30 check1_31)))))

theorem first_inverse (a : Fin 2) (j : Fin (size 0)) :
    (gen 0 a)⁻¹ (label 0 j) = label 0 (next 0 a j) := by
  apply first_inverse_of_check a _ j
  intro k
  have h : checkPow (firstTest a) 0 12 = true := by
    fin_cases a
    · exact checked0
    · exact checked1
  exact checkPow_sound (firstTest a) 12 0 h k.val (Nat.zero_le _)
    (by have := k.isLt; change k.val < 3159 at this; omega)

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.OrbitActions

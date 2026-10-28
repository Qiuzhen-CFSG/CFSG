module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.OrbitActions.Evaluation

/-!
# Checked common-preimage equations for the second orbit

Each check compares short products using already certified actions. These are
literal point comparisons, not assumptions about orders or stabilizers.
Source: ATLAS F24G1-p306936B0, GLS3 Table 5.3v, and the retained orbit trees.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.OrbitActions
open Certificate

-- Keep the bounded numerical reductions sequential.
set_option Elab.async false

private theorem check0_0 : checkPow (secondTest 0) 0 7 = true := by
  decide +kernel

private theorem check0_1 : checkPow (secondTest 0) 128 7 = true := by
  decide +kernel

private theorem check0_2 : checkPow (secondTest 0) 256 7 = true := by
  decide +kernel

private theorem check0_3 : checkPow (secondTest 0) 384 7 = true := by
  decide +kernel

private theorem check0_4 : checkPow (secondTest 0) 512 7 = true := by
  decide +kernel

private theorem check0_5 : checkPow (secondTest 0) 640 7 = true := by
  decide +kernel

private theorem check0_6 : checkPow (secondTest 0) 768 7 = true := by
  decide +kernel

private theorem check0_7 : checkPow (secondTest 0) 896 7 = true := by
  decide +kernel

private theorem checked0 : checkPow (secondTest 0) 0 10 = true :=
  (checkPow_join (secondTest 0) 9 0 (checkPow_join (secondTest 0) 8 0 (checkPow_join (secondTest 0) 7 0 check0_0 check0_1) (checkPow_join (secondTest 0) 7 256 check0_2 check0_3)) (checkPow_join (secondTest 0) 8 512 (checkPow_join (secondTest 0) 7 512 check0_4 check0_5) (checkPow_join (secondTest 0) 7 768 check0_6 check0_7)))

private theorem check1_0 : checkPow (secondTest 1) 0 7 = true := by
  decide +kernel

private theorem check1_1 : checkPow (secondTest 1) 128 7 = true := by
  decide +kernel

private theorem check1_2 : checkPow (secondTest 1) 256 7 = true := by
  decide +kernel

private theorem check1_3 : checkPow (secondTest 1) 384 7 = true := by
  decide +kernel

private theorem check1_4 : checkPow (secondTest 1) 512 7 = true := by
  decide +kernel

private theorem check1_5 : checkPow (secondTest 1) 640 7 = true := by
  decide +kernel

private theorem check1_6 : checkPow (secondTest 1) 768 7 = true := by
  decide +kernel

private theorem check1_7 : checkPow (secondTest 1) 896 7 = true := by
  decide +kernel

private theorem checked1 : checkPow (secondTest 1) 0 10 = true :=
  (checkPow_join (secondTest 1) 9 0 (checkPow_join (secondTest 1) 8 0 (checkPow_join (secondTest 1) 7 0 check1_0 check1_1) (checkPow_join (secondTest 1) 7 256 check1_2 check1_3)) (checkPow_join (secondTest 1) 8 512 (checkPow_join (secondTest 1) 7 512 check1_4 check1_5) (checkPow_join (secondTest 1) 7 768 check1_6 check1_7)))

private theorem inclusion_checked : checkPow inclusionTest 0 10 = true := by
  decide +kernel

/-- The literal 630 labels all occur in the literal 3159-label table. -/
theorem label_inclusion (j : Fin (size 1)) : label 0 (inclusion j) = label 1 j := by
  have h := checkPow_sound inclusionTest 10 0 inclusion_checked j.val (Nat.zero_le _)
    (by have := j.isLt; change j.val < 630 at this; omega)
  simpa only [inclusionTest, Nat.mod_eq_of_lt j.isLt, Fin.eta, decide_eq_true_eq] using h

/-- The stage-three root label is at the advertised stage-two index. -/
theorem inclusion_root : inclusion (root 1) = ⟨1399, by decide⟩ := by decide +kernel

theorem second_inverse
    (ha : ∀ a j, (gen 0 a)⁻¹ (label 0 j) = label 0 (next 0 a j))
    (a : Fin 2) (j : Fin (size 1)) :
    (gen 1 a)⁻¹ (label 1 j) = label 1 (next 1 a j) := by
  apply second_inverse_of_check label_inclusion ha a _ j
  intro k
  have h : checkPow (secondTest a) 0 10 = true := by
    fin_cases a
    · exact checked0
    · exact checked1
  exact checkPow_sound (secondTest a) 10 0 h k.val (Nat.zero_le _)
    (by have := k.isLt; change k.val < 630 at this; omega)

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.OrbitActions

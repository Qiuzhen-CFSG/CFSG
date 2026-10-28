module

public import Theory.Mathieu.M22.Properties.OrderLevel1Data
public import Theory.Mathieu.M22.Properties.OrderLevel1Steps
import Mathlib.Tactic.FinCases

open Theory.GroupTheory

namespace Sporadic.Mathieu

public theorem m22L1_card :
    Nat.card (wordSubgroup m22L1Gen m22L1Inv m22L1Inv_spec) =
      21 * Nat.card (wordSubgroup m22L2Gen m22L2Inv m22L2Inv_spec) :=
  wordSubgroup_card_eq_mul_next
    m22L1Gen m22L1Inv m22L1Inv_spec
    m22L2Gen m22L2Inv m22L2Inv_spec
    m22L1Rep m22L1Act m22L1Factor (2 : Fin 22) m22L1Point (0 : Fin 21)
    (fun r => by rw [m22L1Rep_eq_word r]; exact evalWord_mem_wordSubgroup m22L1Gen m22L1Inv m22L1Inv_spec (m22L1RepWord r))
    (wordSubgroup_le_of_gen_mem (fun i => by rw [m22L2Gen_eq_word i]; exact evalWord_mem_wordSubgroup m22L1Gen m22L1Inv m22L1Inv_spec (m22L2GenWord i)))
    m22L1RepBase m22L1RepPoint m22L1Point_injective
    (wordSubgroup_fix_of_gen_fix m22L2Gen m22L2Inv m22L2Inv_spec (by
      intro i
      fin_cases i <;> rfl))
    m22L1Step

end Sporadic.Mathieu

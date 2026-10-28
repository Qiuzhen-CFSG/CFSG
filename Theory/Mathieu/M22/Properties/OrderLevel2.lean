module

public import Theory.Mathieu.M22.Properties.OrderLevel2Data
public import Theory.Mathieu.M22.Properties.OrderLevel2Steps
import Mathlib.Tactic.FinCases

open Theory.GroupTheory

namespace Sporadic.Mathieu

public theorem m22L2_card :
    Nat.card (wordSubgroup m22L2Gen m22L2Inv m22L2Inv_spec) =
      20 * Nat.card (wordSubgroup m22L3Gen m22L3Inv m22L3Inv_spec) :=
  wordSubgroup_card_eq_mul_next
    m22L2Gen m22L2Inv m22L2Inv_spec
    m22L3Gen m22L3Inv m22L3Inv_spec
    m22L2Rep m22L2Act m22L2Factor (3 : Fin 22) m22L2Point (0 : Fin 20)
    (fun r => by rw [m22L2Rep_eq_word r]; exact evalWord_mem_wordSubgroup m22L2Gen m22L2Inv m22L2Inv_spec (m22L2RepWord r))
    (wordSubgroup_le_of_gen_mem (fun i => by rw [m22L3Gen_eq_word i]; exact evalWord_mem_wordSubgroup m22L2Gen m22L2Inv m22L2Inv_spec (m22L3GenWord i)))
    m22L2RepBase m22L2RepPoint m22L2Point_injective
    (wordSubgroup_fix_of_gen_fix m22L3Gen m22L3Inv m22L3Inv_spec (by
      intro i
      fin_cases i <;> rfl))
    m22L2Step

end Sporadic.Mathieu

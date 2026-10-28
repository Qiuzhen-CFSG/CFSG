module

public import Theory.Mathieu.M22.Properties.OrderLevel3Data
public import Theory.Mathieu.M22.Properties.OrderLevel3Steps
import Mathlib.Tactic.FinCases

open Theory.GroupTheory

namespace Sporadic.Mathieu

public theorem m22L3_card :
    Nat.card (wordSubgroup m22L3Gen m22L3Inv m22L3Inv_spec) =
      16 * Nat.card (wordSubgroup m22L4Gen m22L4Inv m22L4Inv_spec) :=
  wordSubgroup_card_eq_mul_next
    m22L3Gen m22L3Inv m22L3Inv_spec
    m22L4Gen m22L4Inv m22L4Inv_spec
    m22L3Rep m22L3Act m22L3Factor (4 : Fin 22) m22L3Point (0 : Fin 16)
    (fun r => by rw [m22L3Rep_eq_word r]; exact evalWord_mem_wordSubgroup m22L3Gen m22L3Inv m22L3Inv_spec (m22L3RepWord r))
    (wordSubgroup_le_of_gen_mem (fun i => by rw [m22L4Gen_eq_word i]; exact evalWord_mem_wordSubgroup m22L3Gen m22L3Inv m22L3Inv_spec (m22L4GenWord i)))
    m22L3RepBase m22L3RepPoint m22L3Point_injective
    (wordSubgroup_fix_of_gen_fix m22L4Gen m22L4Inv m22L4Inv_spec (by
      intro i
      fin_cases i <;> rfl))
    m22L3Step

end Sporadic.Mathieu

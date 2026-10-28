module

public import Theory.Mathieu.M22.Properties.OrderLevel0Data
public import Theory.Mathieu.M22.Properties.OrderLevel0Steps
import Mathlib.Tactic.FinCases

open Theory.GroupTheory

namespace Sporadic.Mathieu

public theorem m22L0_card :
    Nat.card (wordSubgroup m22L0Gen m22L0Inv m22L0Inv_spec) =
      22 * Nat.card (wordSubgroup m22L1Gen m22L1Inv m22L1Inv_spec) :=
  wordSubgroup_card_eq_mul_next
    m22L0Gen m22L0Inv m22L0Inv_spec
    m22L1Gen m22L1Inv m22L1Inv_spec
    m22L0Rep m22L0Act m22L0Factor (1 : Fin 22) m22L0Point (0 : Fin 22)
    (fun r => by rw [m22L0Rep_eq_word r]; exact evalWord_mem_wordSubgroup m22L0Gen m22L0Inv m22L0Inv_spec (m22L0RepWord r))
    (wordSubgroup_le_of_gen_mem (fun i => by rw [m22L1Gen_eq_word i]; exact evalWord_mem_wordSubgroup m22L0Gen m22L0Inv m22L0Inv_spec (m22L1GenWord i)))
    m22L0RepBase m22L0RepPoint m22L0Point_injective
    (wordSubgroup_fix_of_gen_fix m22L1Gen m22L1Inv m22L1Inv_spec (by
      intro i
      fin_cases i <;> rfl))
    m22L0Step

end Sporadic.Mathieu

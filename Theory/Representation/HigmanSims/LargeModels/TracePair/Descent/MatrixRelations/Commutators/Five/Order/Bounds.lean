module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Arithmetic

/-!
# Width bounds for the fixed right factors

Every coefficient plane of C and C2 is smaller than 2^896. These checked
bounds ensure that simultaneous row multiplication never carries between
lanes. The candidates themselves remain the unchanged `Five.Data` tables.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five

namespace OrderArithmetic

theorem commutatorRows_bounded :
    ∀ r ∈ commutatorRows, r.1 < 2 ^ 896 ∧ r.2 < 2 ^ 896 := by
  have h : commutatorRows.all
      (fun r => decide (r.1 < 2 ^ 896 ∧ r.2 < 2 ^ 896)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem commutatorTwoRows_bounded :
    ∀ r ∈ commutatorTwoRows, r.1 < 2 ^ 896 ∧ r.2 < 2 ^ 896 := by
  have h : commutatorTwoRows.all
      (fun r => decide (r.1 < 2 ^ 896 ∧ r.2 < 2 ^ 896)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

end OrderArithmetic
end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five

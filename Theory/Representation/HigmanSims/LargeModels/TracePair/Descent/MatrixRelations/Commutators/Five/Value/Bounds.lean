module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Arithmetic

/-!
# Width bounds for the four value-product right factors

Each literal coefficient plane is smaller than 2^896. These checked bounds
permit simultaneous lane multiplication by A, B, B² and the candidate B⁴.
Only the numerical tables are used; their intended word values are not inputs.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.ValueArithmetic
open Certificates

theorem generatorRowsA_bounded :
    ∀ r ∈ generatorRowsA, r.1 < 2 ^ 896 ∧ r.2 < 2 ^ 896 := by
  have h : generatorRowsA.all
      (fun r => decide (r.1 < 2 ^ 896 ∧ r.2 < 2 ^ 896)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem generatorRowsB_bounded :
    ∀ r ∈ generatorRowsB, r.1 < 2 ^ 896 ∧ r.2 < 2 ^ 896 := by
  have h : generatorRowsB.all
      (fun r => decide (r.1 < 2 ^ 896 ∧ r.2 < 2 ^ 896)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem bTwoRows_bounded :
    ∀ r ∈ bTwoRows, r.1 < 2 ^ 896 ∧ r.2 < 2 ^ 896 := by
  have h : bTwoRows.all
      (fun r => decide (r.1 < 2 ^ 896 ∧ r.2 < 2 ^ 896)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem bFourRows_bounded :
    ∀ r ∈ bFourRows, r.1 < 2 ^ 896 ∧ r.2 < 2 ^ 896 := by
  have h : bFourRows.all
      (fun r => decide (r.1 < 2 ^ 896 ∧ r.2 < 2 ^ 896)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.ValueArithmetic

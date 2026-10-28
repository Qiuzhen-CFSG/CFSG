module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Products
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order.Rows

/-!
# The fixed degree-896 commutator candidate has fifth power one

Complete kernel-checked numerical certificates prove C*C=C2, C2*C2=C4,
and C4*C=I on the unchanged packed matrices over Four. The existing
`commutator_power_of_checks` then gives C^5=I without any premise.

Identifying C with A*B^4*A*B is independent and remains with `Five.Value`.
The source-word assembly is owned by `Five.lean`. The retained ATLAS source,
certificate construction and measurements are described in `Order/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five
open Certificates OrderRows

/-- All three literal products giving the fifth power of the fixed C. -/
theorem power_checks : ∀ i : Fin 8, 5 ≤ i.val → ProductCheck i := by
  intro i hi
  have h : i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases h with rfl | rfl | rfl
  · exact productCheck_of_rows 5 square_rows
  · exact productCheck_of_rows 6 square_two_rows
  · apply productCheck_of_rows 7
    intro r
    change Streaming.product (commutatorFourRows.getD r.val (0, 0)) commutatorRows =
      identityRows.getD r.val (0, 0)
    rw [four_times_rows r]
    simp [identityRows, r.isLt]

/-- The unconditional fifth-power identity for the unchanged numerical candidate. -/
theorem commutatorRows_pow_five : (Packed.eval 896 commutatorRows) ^ 5 = 1 :=
  commutator_power_of_checks power_checks

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five

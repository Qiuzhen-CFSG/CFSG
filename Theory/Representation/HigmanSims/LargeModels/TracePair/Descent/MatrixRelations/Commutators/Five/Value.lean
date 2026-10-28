module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Products
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.GateZero
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Rows
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value.Sample

/-!
# The five literal commutator-value products

Gate zero reuses the checked shared B² product. Fourteen batches check all
896 rows of each remaining product. The existing matrix-product soundness
theorem and circuit assembly identify the literal candidate with A B⁴ A B.

No generator-order, invertibility or representation assumption is used.
Source: `Five/source/circuit.json` and relator 4 of `Descent/source/HSG1-P1.M`.
Provenance, reproduction and measurements are in `Value/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five
open Certificates

/-- Every fixed product identifying the literal commutator has been checked. -/
theorem value_checks : ∀ i : Fin 8, i.val < 5 → ProductCheck i := by
  intro i hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact value_gate_zero
  · exact productCheck_of_rows 1 ValueRows.square_rows
  · exact productCheck_of_rows 2 ValueRows.left_a_rows
  · exact productCheck_of_rows 3 ValueRows.right_a_rows
  · exact productCheck_of_rows 4 ValueRows.right_b_rows

/-- The fixed candidate is exactly the seven-letter source word. -/
theorem commutator_value :
    Packed.eval 896 generatorRowsA * Packed.eval 896 generatorRowsB ^ 4 *
      Packed.eval 896 generatorRowsA * Packed.eval 896 generatorRowsB =
        Packed.eval 896 commutatorRows :=
  commutator_value_of_checks value_checks

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five

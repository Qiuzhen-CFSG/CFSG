module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Products
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Representative
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Value
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Order

/-!
# Finite-product assembly for the degree-896 commutator fifth power

Two complete batches of literal matrix-product checks establish the exact
source identity. The first identifies C = A B⁴ A B; the second proves C⁵ = I.
Their assembly exports `commutator_five` without premises, preserving the
original matrices over Four and their multiplication order.

Source: relator 4 of the retained ATLAS `Descent/source/HSG1-P1.M`, after the
inverse substitutions proved in `PositiveWords.lean`. See `Five/source/README.md`
for the unchanged source matrices, multiplication circuit and measured checks.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
open Certificates Commutators.Five

/-- Apply the two numerical batches to the literal source relator, in its original order. -/
theorem commutator_five_of_product_checks
    (hv : ∀ i : Fin 8, i.val < 5 → ProductCheck i)
    (hp : ∀ i : Fin 8, 5 ≤ i.val → ProductCheck i) :
    positiveRelation (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) 4 = 1 := by
  change (Packed.eval 896 generatorRowsA * Packed.eval 896 generatorRowsB ^ 4 *
    Packed.eval 896 generatorRowsA * Packed.eval 896 generatorRowsB) ^ 5 = 1
  rw [commutator_value_of_checks hv]
  exact commutator_power_of_checks hp

/-- The literal degree-896 matrices satisfy the source commutator fifth-power relation. -/
theorem commutator_five :
    positiveRelation (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) 4 = 1 :=
  commutator_five_of_product_checks value_checks power_checks

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations

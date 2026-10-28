module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Streaming
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Sample
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.SquareSix

/-!
# The three checked degree-896 commutator relations

The three complete matrix certificates prove the positive words at indices
4, 5 and 6 of the retained HS presentation. A finite case split assembles them
into `commutator_relations`, with no order, invertibility or representation
premise. All use the original packed HSG1-f4r896aB0 matrices over Four.

Source: the commutators `(a,b)^5`, `(a,b*a*b)^3` and `(a,b^2)^6` in
`Descent/source/HSG1-P1.M`. `PositiveWords.relation_eq_positive` proves their
comparison after the independent generator-order checks. The streaming
interfaces and sample remain re-exported; source conventions and bounded
performance measurements are in `Commutators/source/`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
open Certificates

/-- All three positive commutator relations on the retained degree-896 matrices. -/
theorem commutator_relations :
    ∀ i : Fin 13, 4 ≤ i.val → i.val < 7 →
      positiveRelation (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1 := by
  intro i hi hj
  have h : i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases h with rfl | rfl | rfl
  · exact commutator_five
  · exact nested_commutator_three
  · exact square_commutator_six

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations

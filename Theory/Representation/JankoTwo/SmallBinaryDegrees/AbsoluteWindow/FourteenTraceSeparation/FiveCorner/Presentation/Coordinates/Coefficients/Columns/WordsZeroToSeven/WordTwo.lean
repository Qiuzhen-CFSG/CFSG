module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Blocks
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsZeroToSeven.Evaluation
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsZeroToSeven.Coverage

/-!
# Literal catalogue word 2 at every output root

The 126 disjoint blocks contain eight roots each. Each block is checked by the
kernel using the certified packed evaluator; no letters or power pairs are
removed. Block coverage then supplies the complete original WordChecks contract.

Source: Columns/source/README.md and the unchanged Columns/Catalogue.lean.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.WordsZeroToSeven

private theorem blocks0 :
    ∀ q : Fin 32, WordBlock 2 ⟨0 + q.val, by omega⟩ := by
  intro q
  fin_cases q <;> unfold WordBlock <;>
    simp only [← packedColumn_eq] <;> decide +kernel

private theorem blocks32 :
    ∀ q : Fin 32, WordBlock 2 ⟨32 + q.val, by omega⟩ := by
  intro q
  fin_cases q <;> unfold WordBlock <;>
    simp only [← packedColumn_eq] <;> decide +kernel

private theorem blocks64 :
    ∀ q : Fin 32, WordBlock 2 ⟨64 + q.val, by omega⟩ := by
  intro q
  fin_cases q <;> unfold WordBlock <;>
    simp only [← packedColumn_eq] <;> decide +kernel

private theorem blocks96 :
    ∀ q : Fin 30, WordBlock 2 ⟨96 + q.val, by omega⟩ := by
  intro q
  fin_cases q <;> unfold WordBlock <;>
    simp only [← packedColumn_eq] <;> decide +kernel

theorem wordChecks_two : WordChecks 2 :=
  wordChecks_of_quarters 2 blocks0 blocks32 blocks64 blocks96

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.WordsZeroToSeven

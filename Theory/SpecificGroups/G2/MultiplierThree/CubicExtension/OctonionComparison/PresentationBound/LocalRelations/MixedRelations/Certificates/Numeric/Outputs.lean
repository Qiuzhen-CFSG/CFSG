module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Data
/-! The three retained trace outputs have the shared literal word indices.
This is the numeric endpoint premise of `Certificates.local_words_of_numeric`;
the independent word-pool and full trace checks are not asserted here. -/
@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric
theorem outputs : ∀ j : Fin 3, facts (traceOutputs j) = ⟨0, outputWordIndex j, 0, 0⟩ := by
  intro j
  fin_cases j <;> rfl
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric

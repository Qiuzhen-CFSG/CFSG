module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.LatticeData
@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
open Atlas.Codes Atlas.Lattices Atlas.Conway
open scoped Matrix BigOperators
set_option maxRecDepth 100000
theorem sourceVectors_mem (j : Fin 37) : vectorOfData (sourceVectors j) ∈ leech := by
  have hp : ∀ j : Fin 37, ∀ i : Omega,
      vectorOfData (sourceVectors j) i % 2 = sourceParity j := by
    decide +kernel
  have hr : ∀ j : Fin 37,
      halfResidue (vectorOfData (sourceVectors j)) (sourceParity j) =
        wordOfMask (sourceCoeffs j) := by
    decide +kernel
  have hs : ∀ j : Fin 37,
      (∑ i : Omega, vectorOfData (sourceVectors j) i) % 8 = 4 * sourceParity j := by
    decide +kernel
  exact certificate_mem (v := sourceVectors j) (m := sourceParity j) (k := sourceCoeffs j)
    (hp j) (hr j) (hs j)


end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison

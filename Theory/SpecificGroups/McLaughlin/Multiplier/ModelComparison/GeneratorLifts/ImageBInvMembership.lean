module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.LatticeData
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.Check
/-! Kernel-checked Leech congruences for the images of the 37 spanning vectors. -/
@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
open Atlas.Codes Atlas.Lattices Atlas.Conway
open scoped Matrix BigOperators
set_option maxRecDepth 100000
theorem imageBInvVectors_mem (j : Fin 37) : vectorOfData (imageBInvVectors j) ∈ leech := by
  have hp : ∀ j : Fin 37, ∀ i : Omega,
      vectorOfData (imageBInvVectors j) i % 2 = imageBInvParity j := by
    apply allFin
    decide +kernel
  have hr : ∀ j : Fin 37,
      halfResidue (vectorOfData (imageBInvVectors j)) (imageBInvParity j) =
        wordOfMask (imageBInvCoeffs j) := by
    apply allFin
    decide +kernel
  have hs : ∀ j : Fin 37,
      (∑ i : Omega, vectorOfData (imageBInvVectors j) i) % 8 = 4 * imageBInvParity j := by
    apply allFin
    decide +kernel
  exact certificate_mem (v := imageBInvVectors j) (m := imageBInvParity j) (k := imageBInvCoeffs j)
    (hp j) (hr j) (hs j)



end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison

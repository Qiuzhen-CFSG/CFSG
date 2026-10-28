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
theorem imageBVectors_mem (j : Fin 37) : vectorOfData (imageBVectors j) ∈ leech := by
  have hp : ∀ j : Fin 37, ∀ i : Omega,
      vectorOfData (imageBVectors j) i % 2 = imageBParity j := by
    apply allFin
    decide +kernel
  have hr : ∀ j : Fin 37,
      halfResidue (vectorOfData (imageBVectors j)) (imageBParity j) =
        wordOfMask (imageBCoeffs j) := by
    apply allFin
    decide +kernel
  have hs : ∀ j : Fin 37,
      (∑ i : Omega, vectorOfData (imageBVectors j) i) % 8 = 4 * imageBParity j := by
    apply allFin
    decide +kernel
  exact certificate_mem (v := imageBVectors j) (m := imageBParity j) (k := imageBCoeffs j)
    (hp j) (hr j) (hs j)


end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison

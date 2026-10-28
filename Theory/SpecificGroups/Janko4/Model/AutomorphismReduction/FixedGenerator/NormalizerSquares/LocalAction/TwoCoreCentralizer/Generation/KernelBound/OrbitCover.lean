module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorAction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.Coordinates
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.WordEvaluation

/-!
# Full kernel orbit coverage by the twelve local words

The explicit equations in `OrbitCoverCoordinates` recover a mask from any
column satisfying them. Ambient bilinear and exterior-space invariants force
every full-kernel image to satisfy these equations, as proved in
`KernelEquations`. Independently, `WordEvaluation` identifies the specified
local words with the quadratic parametrization in the published column
convention. Applying both results to the recovered mask proves coverage.

The theorem applies to the entire centralizer's canonical homology kernel.
No generation or normality assertion about the full centralizer is assumed.

Source motivation: GLS3, Table 5.3i, printed p.270. Matrix/word attribution
and the direct published-a/column calculation are documented in
`OrbitCover/source/README.md`.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound
open OrbitCoverCoordinates

/-- Global coordinate restrictions and an independent evaluation of the local
words imply coverage, with the mask explicitly extracted from the image column.
The unconditional theorem below supplies both certificate premises. -/
theorem vector_orbit_cover_of_quadratic_certificates
    (hrestriction : ∀ c : homologyAction.ker,
      SatisfiesEquations
        (naturalAction (c : involutionCentralizer) (baseVector : NaturalModule)))
    (hevaluation : ∀ m : OrbitMask,
      representativeVector m = quadraticVector (maskCoordinates m))
    (c : homologyAction.ker) :
    ∃ m : OrbitMask,
      naturalAction (c : involutionCentralizer) (baseVector : NaturalModule) =
        representativeVector m := by
  refine ⟨recoveredMask
    (naturalAction (c : involutionCentralizer) (baseVector : NaturalModule)), ?_⟩
  exact (eq_quadraticVector_recoveredMask (hrestriction c)).trans (hevaluation _).symm

/-- Every image of `(a - 1)e₀` under the full centralizer's homology kernel
is the image under one of the specified increasing-index local words. -/
theorem vector_orbit_cover (c : homologyAction.ker) :
    ∃ m : OrbitMask,
      naturalAction (c : involutionCentralizer) (baseVector : NaturalModule) =
        representativeVector m :=
  vector_orbit_cover_of_quadratic_certificates kernel_image_satisfies_equations
    representativeVector_eq_quadraticVector c

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound

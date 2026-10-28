module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.Contracts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation

/-!
# Matrix equations for the two binary degree-320 actions

The two literal ATLAS matrix pairs must satisfy the seven positive relators
of John Bray's `M24G1-P1`. This finite matrix obligation is independent of
the abstract presentation's comparison with the full Witt-design group.
It assumes neither an action nor irreducibility.

`NativeActions.lean` uses precisely these equations to construct the actions
at the inverse native generators, once the carrier comparison is supplied.
Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/M24G1-P1 and the unchanged
matrix files documented in `Degree320Pair/source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair

/-- All seven positive ATLAS equations for each literal, untransposed matrix pair.
False selects 320a and true selects 320b, as in `matrixA` and `matrixB`. -/
def MatrixRelations : Prop :=
  ∀ variant, Degrees12421792.NativeActions.Presentation.RowRelations
    (matrixA variant) (matrixB variant)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair

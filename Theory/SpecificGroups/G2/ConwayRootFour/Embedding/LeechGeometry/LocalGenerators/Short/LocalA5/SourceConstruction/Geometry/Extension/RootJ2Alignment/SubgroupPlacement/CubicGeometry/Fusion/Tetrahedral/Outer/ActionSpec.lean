module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Tetrahedral.Reference
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Tetrahedral.Outer.Twist

/-!
# The remaining scalar calculation for the explicit semilinear actor

The full scalar A₅ and the lattice actor are fixed concrete maps. This
contract asks for their actual equivariance and a non-inner automorphism
of A₅; it makes no assertion about the reference cubic or its centralizer.
`Outer` supplies the correction, four-point adjustment, and final conditional
application to Aschbacher 49.5, p.284.
-/

@[expose] public noncomputable section
open Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

/-- The specified semilinear lattice actor induces an outer automorphism of
its entire scalar A₅. This is a separate, concrete scalar calculation. -/
def TwistScalarOuterAction : Prop :=
  ∃ α : MulAut (alternatingGroup (Fin 5)),
    (∀ a, MulAut.conj Outer.twistCo1 (scalarFive a) = scalarFive (α a)) ∧
      ∀ a, α ≠ MulAut.conj a

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

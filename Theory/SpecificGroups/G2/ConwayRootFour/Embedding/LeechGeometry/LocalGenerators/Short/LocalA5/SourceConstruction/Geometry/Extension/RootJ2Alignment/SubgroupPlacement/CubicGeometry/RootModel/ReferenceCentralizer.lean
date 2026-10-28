module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.Reference
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Coordinates
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Rigidity
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume

/-!
# From the intrinsic reference action to a faithful special-linear action

The concrete eigenspace action gives matrices of size three without a frame
or a carrier comparison. `Rigidity` proves that integral isometries in its
kernel are central signs, using the invariant pairing and the full fixed-space
kernel theorem. `Volume` proves determinant one using the integral block image
and the rank-24 integral spectral obstruction. The first passes through the
exact central-sign quotient; the second places the matrices in SL₃(4).

Together these results construct the unconditional faithful special-linear
action of the full ambient common centralizer. The application leaf transports
precisely this action to the marked-root bound. The original conditional
assembly remains available with its hypotheses unchanged.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.2, p.280, and the
SL₃(4) action in Lemma 49.5, p.283.
-/

public noncomputable section
open Atlas.Conway Atlas.Lattices Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long

/-- The literal integral kernel and determinant assertions produce the required
embedding of the full ambient common centralizer. Both assertions remain inputs. -/
theorem exists_referenceCentralizerEmbedding_of_eigen_geometry
    (hk : ∀ g : LeechIsometryGroup, leechCentralProjection g ∈ referenceCentralizer →
      (∀ v ∈ fixedSpace,
        quotientModTwoRepresentation referenceCubic v = quotientModTwoRepresentation y v →
          leechModTwoRepresentation g v = v) → g ∈ leechCentralSigns)
    (hd : ∀ g : referenceCentralizer,
      LinearMap.det (referenceEigenAction referenceScalar g).toLinearMap = 1) :
    ∃ j : referenceCentralizer →* SL(3,F), Function.Injective j :=
  ⟨referenceCentralizerToSLOfDet hd,
    referenceCentralizerToSLOfDet_injective hd
      (referenceEigenAction_injective_of_lift_kernel hk)⟩

/-- The actual reference common centralizer acts by determinant-one matrices
on its intrinsic eigenspace, in the published three-dimensional coordinates. -/
def referenceCentralizerToSL : referenceCentralizer →* SL(3,F) :=
  referenceCentralizerToSLOfReferenceEigenAction

/-- The special-linear action retains exactly the original eigenspace matrices. -/
theorem referenceCentralizerToSL_apply (g : referenceCentralizer) :
    (referenceCentralizerToSL g).val = referenceMatrixAction g :=
  referenceCentralizerToSLOfReferenceEigenAction_apply g

/-- The integral sign-kernel theorem makes the full common-centralizer action
faithful after quotienting by exactly the original two central signs. -/
theorem referenceCentralizerToSL_injective :
    Function.Injective referenceCentralizerToSL :=
  referenceCentralizerToSLOfDet_injective referenceEigenAction_det
    referenceEigenAction_injective

/-- The required faithful SL₃(4) action, with both geometric premises discharged. -/
theorem exists_referenceCentralizerEmbedding :
    ∃ j : referenceCentralizer →* SL(3,F), Function.Injective j :=
  ⟨referenceCentralizerToSL, referenceCentralizerToSL_injective⟩

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel

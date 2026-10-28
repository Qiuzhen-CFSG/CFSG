module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer

/-!
# Applying the intrinsic eigenspace action to the marked root cubic

The faithful special-linear action in `ReferenceCentralizer` supplies the
literal homomorphism and injectivity consumed by `RootModel`. Its proved
marking transfers the bound to every supplied carrier equivalence. The
long-cubic application retains the earlier relative fixed-free cubic fusion
input; both the determinant and sign-kernel premises are discharged.

Source: Aschbacher, *Sporadic Groups* (1994), 49.2, p.280, and 49.5, p.283.
The original conditional applications remain available unchanged.
-/

public noncomputable section
open Atlas.Conway Atlas.Lattices Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
open RootModel
open scoped Long

/-- Apply the spectral construction to the original arbitrary marking. -/
theorem rootJ2Cubic_centralizer_card_le_of_referenceEigenGeometry
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (hk : ∀ g : LeechIsometryGroup, leechCentralProjection g ∈ referenceCentralizer →
      (∀ v ∈ fixedSpace,
        quotientModTwoRepresentation referenceCubic v = quotientModTwoRepresentation y v →
          leechModTwoRepresentation g v = v) → g ∈ leechCentralSigns)
    (hd : ∀ g : referenceCentralizer,
      LinearMap.det (referenceEigenAction referenceScalar g).toLinearMap = 1) :
    Nat.card ↥(centralizerI ⊓ Subgroup.centralizer
      (Subgroup.zpowers (rootJ2Cubic e) : Set LeechCentralQuotient)) ≤ Nat.card SL(3,F) := by
  obtain ⟨j, hj⟩ := exists_referenceCentralizerEmbedding_of_eigen_geometry hk hd
  exact rootJ2Cubic_centralizer_card_le_of_referenceEmbedding e j hj

/-- The same two geometric assertions discharge the reference-action premise
of the long-cubic geometry theorem. Relative fusion remains an earlier input. -/
theorem rootJ2_cubicGeometry_of_referenceEigenGeometry (L : LongFrame)
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (hfusion : FixedFreeCubicFusion)
    (hk : ∀ g : LeechIsometryGroup, leechCentralProjection g ∈ referenceCentralizer →
      (∀ v ∈ fixedSpace,
        quotientModTwoRepresentation referenceCubic v = quotientModTwoRepresentation y v →
          leechModTwoRepresentation g v = v) → g ∈ leechCentralSigns)
    (hd : ∀ g : referenceCentralizer,
      LinearMap.det (referenceEigenAction referenceScalar g).toLinearMap = 1) :
    (∃ g ∈ centralizerI, (longCubic L).range ≤
      Sporadic.LeechRelated.J2.RecognitionGeometry.X.map (conjugatedRootJ2 e g)) ∧
    centralizerI ⊓ Subgroup.centralizer ((longCubic L).range : Set LeechCentralQuotient) ≤
      L.long.range := by
  obtain ⟨j, hj⟩ := exists_referenceCentralizerEmbedding_of_eigen_geometry hk hd
  exact rootJ2_cubicGeometry_of_reference L e hfusion j hj

/-- The faithful reference action bounds the full common centralizer of the
marked root cubic for every supplied carrier equivalence. -/
theorem rootJ2Cubic_centralizer_card_le_of_referenceAction
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel) :
    Nat.card ↥(centralizerI ⊓ Subgroup.centralizer
      (Subgroup.zpowers (rootJ2Cubic e) : Set LeechCentralQuotient)) ≤ Nat.card SL(3,F) :=
  rootJ2Cubic_centralizer_card_le_of_referenceEmbedding e
    referenceCentralizerToSL referenceCentralizerToSL_injective

/-- The reference action discharges the common-centralizer bound in the
long-cubic geometry consumer. Relative fixed-free cubic fusion remains explicit. -/
theorem rootJ2_cubicGeometry_of_referenceAction (L : LongFrame)
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (hfusion : FixedFreeCubicFusion) :
    (∃ g ∈ centralizerI, (longCubic L).range ≤
      Sporadic.LeechRelated.J2.RecognitionGeometry.X.map (conjugatedRootJ2 e g)) ∧
    centralizerI ⊓ Subgroup.centralizer ((longCubic L).range : Set LeechCentralQuotient) ≤
      L.long.range :=
  rootJ2_cubicGeometry_of_reference L e hfusion
    referenceCentralizerToSL referenceCentralizerToSL_injective

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction

module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Model
/-!
# Transport of the finite coordinates to the actual scalar field

The entrywise scalarFieldEquiv induces compatible additive coordinates and
an SL₃ group equivalence. Conjugating the finite twist by this equivalence
preserves both literal generator equations. The rational scalar comparison
then turns the finite scalar rule, cubic equation, and axis fixedness into
the complete published FiniteCoordinates record.

The scalar extension lemma keeps the actual inverse-right quaternion
convention, and descends an exact integral basis identity through binaryEquiv.
The final theorem leaves precisely the independent scalar comparison and
four finite embedding certificates explicit; it does not assert their existence.

Source consumer: Aschbacher, Sporadic Groups (1994), 49.5, pp.283–284.
The matrices and integral comparison retain John Bray and Gerald Höhn's ATLAS
attribution and Research and Attribution License 1.0; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Algebra Atlas.Lattices Atlas.Codes Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
namespace ReferenceBlock.ModularCoordinates.FiniteCalculation
open Long.Block Long.Block.Realization

/-- The actual rational extension of the integral scalar representation uses
inverse right multiplication in the displayed quaternion coordinates. -/
theorem scalar_extension_intertwines (u : rationalScalarUnits) (x : Space) :
    (fullIsometryEquiv (icosianScalarsToCo0 u.val)).val (matrixComparison x) =
      matrixComparison (scalarMatrix u *ᵥ x) := by
  rw [icosianScalarsToCo0_extension]
  change icosianComparison (icosianScalarRepresentation u.val
    (icosianComparison.symm (icosianComparison (quaternionComparison x)))) = _
  rw [icosianComparison.symm_apply_apply,
    scalar_intertwines quaternionComparison quaternionComparison_right]
  rfl

/-- An exact rational basis identity gives the literal scalar action modulo two. -/
theorem scalarAction_of_basis (u : rationalScalarUnits) (N : Matrix Index Index ℤ)
    (hN : scalarMatrix u * basisMatrix = basisMatrix * N.map (Int.castRingHom ℚ))
    (v : Binary) : scalarAction u v = N.map (Int.castRingHom Bit) *ᵥ v := by
  change binaryEquiv.symm (leechModTwoRepresentation (icosianScalarsToCo0 u.val)
    (binaryEquiv v)) = _
  rw [binaryEquiv_action _ _ N hN (scalar_extension_intertwines u),
    LinearEquiv.symm_apply_apply]

def goldenVectors : (Fin 3 → F) ≃+ (Fin 3 → GoldenFour) where
  toFun v i := Long.scalarFieldEquiv (v i)
  invFun v i := Long.scalarFieldEquiv.symm (v i)
  left_inv v := by funext i; exact Long.scalarFieldEquiv.symm_apply_apply _
  right_inv v := by funext i; exact Long.scalarFieldEquiv.apply_symm_apply _
  map_add' v w := by funext i; exact map_add Long.scalarFieldEquiv _ _

def goldenMatrices : SL(3,F) ≃* SL(3,GoldenFour) where
  toFun := SpecialLinearGroup.map Long.scalarFieldEquiv.toRingHom
  invFun := SpecialLinearGroup.map Long.scalarFieldEquiv.symm.toRingHom
  left_inv g := by
    apply Subtype.ext
    funext i j
    exact Long.scalarFieldEquiv.symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    funext i j
    exact Long.scalarFieldEquiv.apply_symm_apply _
  map_mul' := (SpecialLinearGroup.map Long.scalarFieldEquiv.toRingHom).map_mul

theorem goldenVectors_smul (a : F) (v : Fin 3 → F) :
    goldenVectors (a • v) = Long.scalarFieldEquiv a • goldenVectors v := by
  funext i
  exact map_mul Long.scalarFieldEquiv _ _

theorem goldenVectors_mulVec (g : SL(3,F)) (v : Fin 3 → F) :
    goldenVectors (g.val *ᵥ v) = (goldenMatrices g).val *ᵥ goldenVectors v := by
  funext i
  change Long.scalarFieldEquiv (∑ j, g.val i j * v j) =
    ∑ j, Long.scalarFieldEquiv (g.val i j) * Long.scalarFieldEquiv (v j)
  simp

theorem goldenMatrices_quotient (g : matrixGroup) :
    goldenMatrices (matrixQuotient g) = goldenQuotient g :=
  matrixQuotient_scalar_map g

def transportedTwist (twist : SL(3,GoldenFour) ≃* SL(3,GoldenFour)) :
    SL(3,F) ≃* SL(3,F) := goldenMatrices.trans (twist.trans goldenMatrices.symm)

theorem goldenMatrices_twist (twist : SL(3,GoldenFour) ≃* SL(3,GoldenFour)) (g : SL(3,F)) :
    goldenMatrices (transportedTwist twist g) = twist (goldenMatrices g) :=
  goldenMatrices.apply_symm_apply _

/-- Transport every clause through the actual field equivalence and the
proved scalar comparison on the quaternion-fixed vectors. -/
def GoldenCoordinates.toFinite {inverse opposite : Bool}
    (c : GoldenCoordinates inverse opposite) (h : ScalarComparison)
    (u : rationalScalarUnits)
    (hu : ∀ v, AxisFixed v → scalarAction u v = orientationAction opposite v) :
    FiniteCoordinates inverse u where
  embed := c.embed.comp goldenVectors.toAddMonoidHom
  injective := c.injective.comp goldenVectors.injective
  twist := transportedTwist c.twist
  fixed v := h.fixed _ (c.fixed (goldenVectors v))
  scalar a v := by
    change c.embed (goldenVectors (a • v)) =
      (Long.scalarFieldEquiv a).re • c.embed (goldenVectors v) +
        (Long.scalarFieldEquiv a).im • scalarAction u (c.embed (goldenVectors v))
    rw [goldenVectors_smul, c.scalar, hu _ (c.fixed _)]
  cubic v := by
    exact (c.cubic (goldenVectors v)).trans (hu _ (c.fixed _)).symm
  generatorA v := by
    change generatorACoordinates.map (Int.castRingHom Bit) *ᵥ c.embed (goldenVectors v) =
      c.embed (goldenVectors ((transportedTwist c.twist (matrixQuotient matrixGeneratorA)).val *ᵥ v))
    rw [c.generatorA, goldenVectors_mulVec, goldenMatrices_twist,
      goldenMatrices_quotient, goldenQuotient_generatorA]
  generatorB v := by
    change generatorBCoordinates.map (Int.castRingHom Bit) *ᵥ c.embed (goldenVectors v) =
      c.embed (goldenVectors ((transportedTwist c.twist (matrixQuotient matrixGeneratorB)).val *ᵥ v))
    rw [c.generatorB, goldenVectors_mulVec, goldenMatrices_twist,
      goldenMatrices_quotient, goldenQuotient_generatorB]

end ReferenceBlock.ModularCoordinates.FiniteCalculation
open ReferenceBlock.ModularCoordinates.FiniteCalculation
namespace ReferenceBlock.ModularCoordinates
/-- Assembly of the independent finite and rational-scalar calculations. -/
theorem finiteCoordinates_of_comparisons (h : ScalarComparison)
    (hc : ∀ inverse opposite : Bool, Nonempty (GoldenCoordinates inverse opposite))
    (inverse : Bool) (u : Long.Block.Realization.rationalScalarUnits)
    (hu : orderOf (Long.Block.Realization.rationalScalarToFive u) = 3) :
    Nonempty (FiniteCoordinates inverse u) := by
  obtain ⟨opposite, ho⟩ := h.cubic u hu
  obtain ⟨c⟩ := hc inverse opposite
  exact ⟨c.toFinite h u ho⟩
end ReferenceBlock.ModularCoordinates
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel

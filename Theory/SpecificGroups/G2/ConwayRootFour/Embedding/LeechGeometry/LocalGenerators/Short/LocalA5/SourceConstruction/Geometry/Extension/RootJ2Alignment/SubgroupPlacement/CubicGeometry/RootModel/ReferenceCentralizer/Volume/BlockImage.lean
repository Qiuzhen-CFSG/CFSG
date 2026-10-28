module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.Coordinates
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.IntegralAlignment
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates

/-!
# Special-linear image containment from an integral block comparison

The two-generator coordinate comparison identifies the actual eigenspace with
F₄³. Its trivial padding is consequently zero. To realize a matrix in the
published arbitrary referenceBasis, conjugate it into the supplied coordinates.
Conjugation preserves determinant one, and matrixQuotient_surjective then
provides an actual integral block element with the requested matrix.

The imported integral-alignment and modular-coordinate modules construct the
two geometric inputs unconditionally. The assembly below applies them to the
published arbitrary basis. The final theorem applies this precise containment
to the published determinant reduction, leaving the independent integral Singer
exclusion explicit.

Source: Aschbacher, *Sporadic Groups* (1994), 49.2, p.280, and 49.5,
pp.283–284. The exact integral matrices and comparisons retain the imported
John Bray and Gerald Höhn ATLAS attribution and license.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Atlas.Conway Atlas.Algebra Atlas.Lattices Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
namespace ReferenceBlock

private theorem padding_zero (e : (Fin 3 → F) ≃ₗ[F] ReferenceNatural)
    (v : ReferencePadding) : v = 0 := by
  have hd : Module.finrank F ReferenceNatural = 3 := by
    rw [← e.finrank_eq]
    simp
  funext i
  have hi := i.isLt
  change i.val < 3 - Module.finrank F ReferenceNatural at hi
  omega

private def paddedEquiv (e : (Fin 3 → F) ≃ₗ[F] ReferenceNatural) :
    (Fin 3 → F) ≃ₗ[F] ReferencePadded where
  toFun v := (e v, 0)
  invFun w := e.symm w.1
  left_inv v := e.symm_apply_apply v
  right_inv w := Prod.ext (e.apply_symm_apply w.1) (padding_zero e w.2).symm
  map_add' v w := Prod.ext (map_add e v w) (by simp)
  map_smul' a v := Prod.ext (map_smul e a v) (by simp)

/-- A proved integral alignment and two checked generator actions suffice for
coverage in the published arbitrary basis, including its trivial padding. -/
theorem coverage_of_coordinates (d : Alignment) (c : Coordinates d) :
    ReferenceSpecialLinearCoverage := by
  intro A
  let e := paddedEquiv c.equiv
  let f : Module.End F ReferencePadded := Matrix.toLin referenceBasis referenceBasis A.val
  let h : Module.End F (Fin 3 → F) :=
    e.symm.toLinearMap ∘ₗ f ∘ₗ e.toLinearMap
  have hhdet : (LinearMap.toMatrix' h).det = 1 := by
    rw [LinearMap.det_toMatrix']
    change LinearMap.det (e.symm.toLinearMap ∘ₗ f ∘ₗ e.symm.symm.toLinearMap) = 1
    rw [LinearMap.det_conj, LinearMap.det_toLin]
    exact A.property
  let B : SL(3,F) := ⟨LinearMap.toMatrix' h, hhdet⟩
  obtain ⟨g, hg⟩ := Long.Block.matrixQuotient_surjective (c.twist.symm B)
  have htw : c.twist (Long.Block.matrixQuotient g) = B := by
    rw [hg, c.twist.apply_symm_apply]
  have hp (v : Fin 3 → F) :
      referencePaddedAction (toReference d g) (e v) = e (B.val *ᵥ v) := by
    apply Prod.ext
    · change referenceEigenAction referenceScalar (toReference d g) (c.equiv v) =
        c.equiv (B.val *ᵥ v)
      rw [c.intertwines, htw]
    · rfl
  have hf : (referencePaddedAction (toReference d g)).toLinearMap = f := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [LinearEquiv.coe_coe, hp]
    have hb : B.val *ᵥ w = e.symm (f (e w)) := LinearMap.toMatrix'_mulVec h w
    rw [hb, e.apply_symm_apply]
  refine ⟨toReference d g, ?_⟩
  change LinearMap.toMatrix referenceBasis referenceBasis
    (referencePaddedAction (toReference d g)).toLinearMap = A.val
  rw [hf]
  exact LinearMap.toMatrix_toLin referenceBasis referenceBasis A.val

end ReferenceBlock

/-- The explicit integral block realizes every special-linear matrix in the
literal reference eigenspace action. -/
theorem referenceSpecialLinearCoverage : ReferenceSpecialLinearCoverage := by
  let d := referenceBlockAlignment
  obtain ⟨c⟩ := referenceBlockCoordinates d
  exact ReferenceBlock.coverage_of_coordinates d c


/-- The block comparison discharges precisely the special-linear coverage
premise of the existing full-centralizer determinant reduction. -/
theorem referenceEigenAction_det_of_blockCoordinates_and_integral_obstruction
    (d : ReferenceBlock.Alignment) (c : ReferenceBlock.Coordinates d)
    (hint : ReferenceSingerExcluded) (g : referenceCentralizer) :
    LinearMap.det (referenceEigenAction referenceScalar g).toLinearMap = 1 :=
  referenceEigenAction_det_of_block_and_integral_obstruction
    (ReferenceBlock.coverage_of_coordinates d c) hint g

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel


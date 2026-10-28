module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Coordinates
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.Singer

/-!
# Determinant reduction for the full reference common centralizer

A subgroup of GL₃(4) containing SL₃(4) either has only determinant one or
contains the explicit Singer matrix from `Volume.Singer`. Here this elementary
argument is applied to the literal padded eigenspace action. A determinant
other than one can be squared to obtain ω, then corrected by an element of
SL₃(4) to give the specified matrix. The resulting conditional theorem feeds
the existing `referenceCentralizerToSLOfDet` without changing its matrices.

The special-linear image containment and integral exclusion remain separate
geometric premises. This module does not prove either premise or the
unconditional determinant theorem. In particular it does not infer determinant
one from a pairing between the two eigenspaces.

Source consumer: Aschbacher, *Sporadic Groups* (1994), 49.2, p.280, and
49.5, p.283. The exact integral and scalar conventions are those of the
imported reference action.
-/

@[expose] public noncomputable section
open Atlas.Algebra Atlas.Conway Atlas.Lattices Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long

private theorem scalar_cases (a : F) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    a = referenceScalar ∨ a = referenceScalar ^ 2 := by
  have h : ∀ c : GoldenFour, c ≠ 0 → c ≠ 1 →
      c = goldenFourTau ∨ c = goldenFourTau ^ 2 := by decide +kernel
  have hh := h (Long.scalarFieldEquiv a)
    (fun he => h0 (Long.scalarFieldEquiv.injective (he.trans (map_zero _).symm)))
    (fun he => h1 (Long.scalarFieldEquiv.injective (he.trans (map_one _).symm)))
  rcases hh with hh | hh
  · left
    apply Long.scalarFieldEquiv.injective
    simpa only [referenceScalar, RingEquiv.apply_symm_apply] using hh
  · right
    apply Long.scalarFieldEquiv.injective
    simpa only [map_pow, referenceScalar, RingEquiv.apply_symm_apply] using hh

/-- Invertibility on the actual eigenspace makes its matrix determinant nonzero. -/
theorem referenceMatrixAction_det_ne_zero (g : referenceCentralizer) :
    (referenceMatrixAction g).det ≠ 0 := by
  rw [referenceMatrixAction_det]
  exact (referenceEigenAction referenceScalar g).isUnit_det'.ne_zero

/-- Coverage of the determinant-one matrices in the existing coordinates. -/
def ReferenceSpecialLinearCoverage : Prop :=
  ∀ A : SL(3,F), ∃ g : referenceCentralizer, referenceMatrixAction g = A.val

/-- The single forbidden matrix, measured in the actual padded coordinates. -/
def ReferenceSingerExcluded : Prop :=
  ∀ g : referenceCentralizer, referenceMatrixAction g ≠ referenceSinger

private theorem exists_scalar_determinant (g : referenceCentralizer)
    (hg : (referenceMatrixAction g).det ≠ 1) :
    ∃ h : referenceCentralizer, (referenceMatrixAction h).det = referenceScalar := by
  rcases scalar_cases _ (referenceMatrixAction_det_ne_zero g) hg with h | h
  · exact ⟨g, h⟩
  · refine ⟨g ^ 2, ?_⟩
    rw [map_pow, Matrix.det_pow, h, ← pow_mul]
    change referenceScalar ^ (3 + 1) = referenceScalar
    rw [pow_succ, referenceScalar_cube, one_mul]

/-- Once all special-linear matrices occur, a nontrivial determinant produces
the fixed Singer matrix by a determinant-one correction. -/
theorem exists_referenceSinger_of_nontrivial_det
    (hblock : ReferenceSpecialLinearCoverage) (g : referenceCentralizer)
    (hg : (referenceMatrixAction g).det ≠ 1) :
    ∃ h : referenceCentralizer, referenceMatrixAction h = referenceSinger := by
  obtain ⟨k, hk⟩ := exists_scalar_determinant g hg
  have hinv : (referenceMatrixAction k⁻¹).det * (referenceMatrixAction k).det = 1 := by
    rw [← Matrix.det_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.det_one]
  let B : SL(3,F) := ⟨referenceMatrixAction k⁻¹ * referenceSinger, by
    rw [Matrix.det_mul, referenceSinger_det, ← hk]
    exact hinv⟩
  obtain ⟨b, hb⟩ := hblock B
  refine ⟨k * b, ?_⟩
  rw [map_mul, hb]
  change referenceMatrixAction k * (referenceMatrixAction k⁻¹ * referenceSinger) = _
  rw [← Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mul]

/-- The two independent geometric inputs discharge exactly the determinant
premise of `referenceCentralizerToSLOfDet`. Neither input is asserted here. -/
theorem referenceEigenAction_det_of_block_and_integral_obstruction
    (hblock : ReferenceSpecialLinearCoverage) (hint : ReferenceSingerExcluded)
    (g : referenceCentralizer) :
    LinearMap.det (referenceEigenAction referenceScalar g).toLinearMap = 1 := by
  rw [← referenceMatrixAction_det]
  by_contra hg
  obtain ⟨h, hh⟩ := exists_referenceSinger_of_nontrivial_det hblock g hg
  exact hint h hh

/-- Apply the determinant criterion to the existing full-centralizer homomorphism. -/
def referenceCentralizerToSLOfBlockAndIntegralObstruction
    (hblock : ReferenceSpecialLinearCoverage) (hint : ReferenceSingerExcluded) :
    referenceCentralizer →* SL(3,F) :=
  referenceCentralizerToSLOfDet
    (referenceEigenAction_det_of_block_and_integral_obstruction hblock hint)

/-- The conditional special-linear action retains exactly the original matrices. -/
theorem referenceCentralizerToSLOfBlockAndIntegralObstruction_apply
    (hblock : ReferenceSpecialLinearCoverage) (hint : ReferenceSingerExcluded)
    (g : referenceCentralizer) :
    (referenceCentralizerToSLOfBlockAndIntegralObstruction hblock hint g).val =
      referenceMatrixAction g := rfl

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel

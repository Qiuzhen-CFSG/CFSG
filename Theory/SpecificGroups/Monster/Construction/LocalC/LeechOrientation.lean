module

public import Theory.SpecificGroups.Monster.Construction.LocalC.RealLeech.Extension
public import Theory.SpecificGroups.Monster.Construction.LocalC.LeechOrientation.Rational

/-!
# Orientation of the fixed real Leech action

The fixed real extension is the rational extension with its matrix entries
cast to the reals and its coordinates reindexed by `coordinateMarking`.
Both operations preserve the determinant, so rational orientation gives
orientation of the full Leech isometry action used in the local pullback.

Source: Aschbacher, *Sporadic Groups*, Sections 22–23 and the stabilizer `C₂`
in `SL(B₁²⁴)` in Section 27, printed pp. 147–148.
-/

public section
noncomputable section
open Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC

/-- The full integral Leech isometry group acts with determinant one on the fixed real space. -/
@[simp] theorem realLeechRepresentation_det (g : LeechIsometryGroup) :
    LinearMap.det (realLeechRepresentation g).toLinearMap = 1 := by
  change LinearMap.det (Matrix.mulVecLin (realLeechMatrix g)) = 1
  rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
  unfold realLeechMatrix
  rw [Matrix.det_submatrix_equiv_self]
  have he := (Rat.castHom ℝ).map_det
    (LinearMap.toMatrix' (fullIsometryEquiv g).val.toLinearMap)
  change _ = ((LinearMap.toMatrix' (fullIsometryEquiv g).val.toLinearMap).map
    (Rat.castHom ℝ)).det at he
  rw [← he, LinearMap.det_toMatrix']
  change ((LinearMap.det (rationalExtension g.val).toLinearMap : ℚ) : ℝ) = 1
  rw [rationalExtension_det_one]
  norm_num

end Sporadic.Monster.Construction.LocalC

module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.WordDescent

/-!
# Coordinates of the literal F4 Chevalley carrier

The carrier is presented inside a general linear variety using a reindexed
basis of the integral Geck lattice. Its matrix coordinates are precisely the
entries of `pointMatrix` under that reindexing. Its remaining coordinate is
the inverse determinant, hence the determinant of the inverse point matrix.
These comparisons include every presented coordinate and permit polynomial
matrix calculations to establish regularity on the literal carrier.

This supplies the presentation comparison used in the exceptional morphism
of GLS3, Theorem 1.15.4(b) (`refs/KGroup/GLS3/Chapter1.tex`).
-/

public section

open scoped Classical Matrix
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction ReeF4.WordRelations
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F]

private theorem ambientUnits_coordinate (g : (Matrix Coordinate Coordinate F)ˣ)
    (hg : g ∈ matrixGroup F)
    (i j : Fin (Module.finrank F (Coordinate → F))) :
    (ambientUnitsEquiv g).val (Sum.inl (i, j)) =
      g.val ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := F)).symm i)
        ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := F)).symm j) := by
  let e : (Matrix Coordinate Coordinate F)ˣ ≃* Variety.Point (F4Chevalley.Ambient F) :=
    Matrix.GeneralLinearGroup.toLin.trans
      ((Matrix.GeneralLinearGroup.toLin'
        (carrierBasis (P := typeF4RootPairing) (b := typeF4RootPairing_base))).symm.trans
        (translationGLPointMulEquiv _).symm)
  have he : ambientUnitsEquiv g = e g := by
    change g ∈ Subgroup.closure (Set.range fun rt : F4Chevalley.Root × F =>
      F4Chevalley.rootCurve rt.1 rt.2) at hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
        rcases hg with ⟨⟨r, t⟩, rfl⟩
        rw [ambientUnitsEquiv_rootCurve, F4Chevalley.ambientRootMorphism_apply]
        rfl
    | one => simp only [map_one]
    | mul g h _ _ hg hh => simp only [map_mul, hg, hh]
    | inv g _ hg => simp only [map_inv, hg]
  rw [he]
  change (generalLinearRepresentationPoint _ (Matrix.GeneralLinearGroup.toLin g)).val _ = _
  rw [generalLinearRepresentationPoint_matrix]
  simp [carrierBasis, Module.Basis.reindex_apply]

/-- Matrix entries are literal presented coordinates after the fixed basis
reindexing. -/
theorem pointMatrix_coordinate (x : PointGroup F) (i j : Coordinate) :
    (pointMatrix x).val i j = x.val (Sum.inl
      (carrierIndexEquiv (b := typeF4RootPairing_base) (k := F) i,
       carrierIndexEquiv (b := typeF4RootPairing_base) (k := F) j)) := by
  have h := ambientUnits_coordinate (pointMatrix x) (pointMatrix_mem x)
    (carrierIndexEquiv (b := typeF4RootPairing_base) (k := F) i)
    (carrierIndexEquiv (b := typeF4RootPairing_base) (k := F) j)
  simp only [Equiv.symm_apply_apply] at h
  have he : ambientUnitsEquiv (pointMatrix x) =
      (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints x :=
    ambientUnitsEquiv.apply_symm_apply _
  rw [he] at h
  exact h.symm

/-- Conversely, every matrix coordinate of the presentation is an entry of
the faithful point matrix. -/
theorem point_coordinate_matrix (x : PointGroup F)
    (i j : Fin (Module.finrank F (Coordinate → F))) :
    x.val (Sum.inl (i, j)) = (pointMatrix x).val
      ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := F)).symm i)
      ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := F)).symm j) := by
  rw [pointMatrix_coordinate]
  simp only [Equiv.apply_symm_apply]

/-- The extra general-linear coordinate is the determinant of the inverse
point matrix; it is not discarded by the matrix realization. -/
theorem point_auxiliary_coordinate (x : PointGroup F) :
    x.val (Sum.inr PUnit.unit) = ((pointMatrix x⁻¹).val).det := by
  let y := (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints x
  have he : glMatrixOfPoint (Module.finrank F (Coordinate → F)) y =
      Matrix.reindex (carrierIndexEquiv (b := typeF4RootPairing_base) (k := F))
        (carrierIndexEquiv (b := typeF4RootPairing_base) (k := F)) (pointMatrix x).val := by
    ext i j
    exact point_coordinate_matrix x i j
  change glScalarOfPoint _ y = _
  rw [glScalarOfPoint_eq_inv_det, he, Matrix.det_reindex_self, map_inv]
  simp
end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism

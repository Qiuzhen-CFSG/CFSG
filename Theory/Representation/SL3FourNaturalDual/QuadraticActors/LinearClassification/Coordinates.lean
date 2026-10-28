module

public import Theory.Representation.SL3FourNaturalDual.Markings
public import Mathlib.LinearAlgebra.Determinant

/-!
# Equivariant changes of coordinates for the SL₃(4) natural-plus-dual module

Every F₄-linear equivalence of the natural space induces an automorphism of
the determinant-one matrix group. Pairing with the natural space constructs
the contragredient coordinates on the dual summand and proves the full
intertwining equation. In particular, these changes do not require the
coordinate matrix itself to have determinant one.

This is the coordinate-transport step in the root-plane argument of
Aschbacher--Smith, proof of 13.8.20, printed p.955 (PDF p.972).
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification
open Matrix

def conjugateMatrix (e : W ≃ₗ[F] W) (g : SL) : SL :=
  ⟨LinearMap.toMatrix' (e.conj (Matrix.toLin' g.val)), by
    rw [LinearMap.det_toMatrix', LinearEquiv.conj_apply]
    change LinearMap.det (e.toLinearMap.comp ((Matrix.toLin' g.val).comp
      e.symm.toLinearMap)) = 1
    rw [LinearMap.det_conj, LinearMap.det_toLin']
    exact g.property⟩

lemma conjugateMatrix_apply (e : W ≃ₗ[F] W) (g : SL) (w : W) :
    (conjugateMatrix e g).val.mulVec w = e (g.val.mulVec (e.symm w)) := by
  exact LinearMap.toMatrix'_mulVec _ _

lemma conjugateMatrix_symm (e : W ≃ₗ[F] W) (g : SL) :
    conjugateMatrix e.symm (conjugateMatrix e g) = g := by
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  change (conjugateMatrix e.symm (conjugateMatrix e g)).val.mulVec w = g.val.mulVec w
  simp only [conjugateMatrix_apply, LinearEquiv.symm_symm, e.symm_apply_apply]

/-- Conjugation of SL by arbitrary invertible F₄-linear coordinates. -/
def coordinateAut (e : W ≃ₗ[F] W) : SL ≃* SL where
  toFun := conjugateMatrix e
  invFun := conjugateMatrix e.symm
  left_inv := conjugateMatrix_symm e
  right_inv := conjugateMatrix_symm e.symm
  map_mul' g h := by
    apply Subtype.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro w
    change (conjugateMatrix e (g*h)).val.mulVec w =
      ((conjugateMatrix e g).val * (conjugateMatrix e h).val).mulVec w
    rw [← Matrix.mulVec_mulVec, conjugateMatrix_apply, conjugateMatrix_apply,
      conjugateMatrix_apply, e.symm_apply_apply, Matrix.mulVec_mulVec]
    rfl

lemma coordinateAut_natural (e : W ≃ₗ[F] W) (g : SL) (w : W) :
    (coordinateAut e g).val.mulVec w = e (g.val.mulVec (e.symm w)) :=
  conjugateMatrix_apply e g w

/-- The contragredient coordinates associated to a natural coordinate change. -/
def dualChange (e : W ≃ₗ[F] W) : W ≃ₗ[F] W :=
  ((dotProductEquiv F (Fin 3)).trans e.symm.dualMap).trans
    (dotProductEquiv F (Fin 3)).symm

lemma dualChange_pair (e : W ≃ₗ[F] W) (w x : W) :
    dualChange e w ⬝ᵥ x = w ⬝ᵥ e.symm x := by
  change dotProductEquiv F (Fin 3) (dualChange e w) x = _
  simp only [dualChange, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.dualMap_apply]
  rfl

lemma dualChange_equivariant (e : W ≃ₗ[F] W) (g : SL) (w : W) :
    dualChange e (dualCoordinates g w) =
      dualCoordinates (coordinateAut e g) (dualChange e w) := by
  apply (dotProductEquiv F (Fin 3)).injective
  apply LinearMap.ext
  intro x
  change dualChange e (dualCoordinates g w) ⬝ᵥ x =
    ((coordinateAut e g)⁻¹).val.transpose.mulVec (dualChange e w) ⬝ᵥ x
  rw [dualChange_pair, dotProduct_comm _ x, Matrix.dotProduct_transpose_mulVec,
    dualChange_pair, ← map_inv, coordinateAut_natural, e.symm_apply_apply]
  change (g⁻¹).val.transpose.mulVec w ⬝ᵥ e.symm x =
    w ⬝ᵥ (g⁻¹).val.mulVec (e.symm x)
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]

/-- The natural and contragredient coordinate changes on the actual module. -/
def coordinateChange (e : W ≃ₗ[F] W) : V ≃ₗ[ZMod 2] V :=
  (e.prodCongr (dualChange e)).restrictScalars (ZMod 2)

lemma coordinateChange_equivariant (e : W ≃ₗ[F] W) (g : SL) (v : V) :
    coordinateChange e (representation g v) =
      representation (coordinateAut e g) (coordinateChange e v) := by
  apply Prod.ext
  · change e (g.val.mulVec v.1) = (coordinateAut e g).val.mulVec (e v.1)
    rw [coordinateAut_natural, e.symm_apply_apply]
  · exact dualChange_equivariant e g v.2

/-- A genuine marking in the direction used by `CriticalShapes`. -/
def coordinateMarking (e : W ≃ₗ[F] W) : LinearMarking representation where
  actor := (coordinateAut e).symm.toMonoidHom
  coordinates := coordinateChange e
  equivariant g v := by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using
      coordinateChange_equivariant e ((coordinateAut e).symm g) v

end Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification

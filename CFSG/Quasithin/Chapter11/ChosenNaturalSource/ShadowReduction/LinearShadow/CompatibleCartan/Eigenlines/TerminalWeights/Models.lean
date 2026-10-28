module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.SeparateActions
public import Theory.Representation.OrthogonalFourPlusMatrix.Action
public import Mathlib.LinearAlgebra.Determinant
/-!
# Determinants and eigenvalues through the common-field construction

The left-right action on two-by-two matrices has linear determinant one:
row coordinates compute the determinant of right multiplication, and
transpose conjugation gives left multiplication. This is a determinant
of the four-dimensional action, distinct from preservation of the
quadratic form on vector matrices.

Changing coefficients by the restriction isomorphism transports both
that determinant and every eigenvalue. Multiplicative orders are preserved.
TerminalWeights.Source applies these formulas to the actual marked P.

Source: Aschbacher--Smith, Proposition 11.3.2, final paragraph, printed p.775.
-/
open Subgroup Representation
open scoped IsMulCommutative
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
open ClassicalOrthogonal.FourPlusMatrix Matrix
variable {F : Type*} [Field F]
private theorem right_det (A : Mat (F := F)) :
    LinearMap.det (LinearMap.mulRight F A) = A.det ^ 2 := by
  let e : Mat (F := F) ≃ₗ[F] ((Fin 2 → F) × (Fin 2 → F)) :=
    LinearEquiv.finTwoArrow F (Fin 2 → F)
  have he : e.toLinearMap ∘ₗ (LinearMap.mulRight F A) ∘ₗ e.symm.toLinearMap =
      LinearMap.prodMap (Matrix.toLin' A.transpose) (Matrix.toLin' A.transpose) := by
    apply LinearMap.ext
    rintro ⟨u,v⟩
    apply Prod.ext <;> ext j <;>
      simp [e,LinearEquiv.finTwoArrow,LinearMap.mulRight_apply,Matrix.mul_apply,
        Matrix.toLin'_apply,Matrix.mulVec,dotProduct,mul_comm]
  have hd := congrArg LinearMap.det he
  rw [LinearMap.det_conj,LinearMap.det_prodMap,LinearMap.det_toLin',Matrix.det_transpose] at hd
  simpa only [sq] using hd

private theorem left_det (A : Mat (F := F)) :
    LinearMap.det (LinearMap.mulLeft F A) = A.det ^ 2 := by
  let e := Matrix.transposeLinearEquiv (Fin 2) (Fin 2) F F
  have he : e.toLinearMap ∘ₗ (LinearMap.mulLeft F A) ∘ₗ e.symm.toLinearMap =
      LinearMap.mulRight F A.transpose := by
    ext M i j
    exact congrFun (congrFun (Matrix.transpose_mul A M.transpose) i) j
  have hd := congrArg LinearMap.det he
  rw [LinearMap.det_conj, right_det,Matrix.det_transpose] at hd
  exact hd

/-- The determinant of the linear four-space action, not of a vector matrix. -/
theorem matrix_action_det (g : PairSL (F := F)) :
    LinearMap.det (representation g) = 1 := by
  have he : representation g =
      (LinearMap.mulRight F g.2⁻¹.val).comp (LinearMap.mulLeft F g.1.val) := rfl
  rw [he,LinearMap.det_comp,right_det,left_det,g.1.det_coe,g.2⁻¹.det_coe]
  simp
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
section Transport
variable {E F M : Type*} [Field E] [Field F] [Finite F]
  [AddCommGroup M] [Module E M] [Module.Finite E M]
  (N : NaturalPlane (E := E) (F := F) (A := M)) (hc : Nat.card E = Nat.card F)

omit [Module.Finite E M] in
theorem compatible_smul (a : E) (v : M) :
    letI := N.compatibleModule hc
    N.fieldEquiv hc a • v = a • v := by
  change (N.fieldEquiv hc).symm (N.fieldEquiv hc a) • v = a • v
  rw [RingEquiv.symm_apply_apply]

/-- The determinant is transported by the restriction field isomorphism. -/
theorem compatible_det (t : Module.End E M) :
    letI := N.compatibleModule hc
    LinearMap.det (N.compatibleEnd hc t) = N.fieldEquiv hc t.det := by
  let := N.compatibleModule hc
  let b := Module.finBasis E M
  let b' := b.mapCoeffs (N.fieldEquiv hc) (compatible_smul N hc)
  rw [←LinearMap.det_toMatrix b',←LinearMap.det_toMatrix b]
  rw [RingEquiv.map_det]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply,b',Module.Basis.mapCoeffs_apply,Module.Basis.mapCoeffs_repr]
  rfl

omit [Module.Finite E M] in
theorem compatible_eigenvalue (t : Module.End E M) (a : E) (v : M)
    (hv : t v = a • v) :
    letI := N.compatibleModule hc
    N.compatibleEnd hc t v = N.fieldEquiv hc a • v := by
  let := N.compatibleModule hc
  change t v = N.fieldEquiv hc a • v
  rw [compatible_smul N hc]
  exact hv

omit [Module.Finite E M] in
theorem compatible_orderOf (a : E) : orderOf (N.fieldEquiv hc a) = orderOf a :=
  orderOf_injective (N.fieldEquiv hc).toMonoidHom (N.fieldEquiv hc).injective a
end Transport

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights

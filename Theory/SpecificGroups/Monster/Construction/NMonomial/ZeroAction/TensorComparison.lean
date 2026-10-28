module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.Forms
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.HalfComparisons
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The corrected natural--half-spin comparison

The involution `b ↦ b + epsilon_x(b)` on the actual Parker loop carries
multiplication by Omega to multiplication by signed Omega and commutes with
the central sign. It therefore induces an isometry between the two actual
second-axis half-spin modules. Applying it separately at each marked natural
coordinate gives the corrected tensor comparison of 29.7(1).

`sourceTensorComparison_delta` states the formula on the literal natural
halfspace vectors and signed spin vectors, using the fixed Leech coordinate
marking. This module proves descent, the linear equivalence and its form
identity. Equivariance under NPlus and assembly of the full N-action are
separate obligations; they do not follow just from the linear comparison.

Source: Aschbacher, *Sporadic Groups*, 29.7(1), printed p. 156 (PDF page 84,
left). The book's right-action product acts from left to right. The repository
uses left function composition, so its collected word corresponding to
`psi_1(d) psi_2(e) psi_1(alpha)` is
`psiAut1N alpha * psi2N e * psi1N d`. Source conjugation is consequently
translated to `g * r * g^-1` on the actual permutations.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer
open Sporadic.Monster.Construction
open LocalC ShortFamilies TrialitySpin SpinActions
open scoped TensorProduct
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction

def correction (x : Omega) (b : ParkerLoop) : ParkerLoop := parkerSign (b.1.val x) b

theorem correction_involutive (x : Omega) : Function.Involutive (correction x) := by
  intro b
  simp [correction, parkerSign, add_assoc]

def correctionEquiv (x : Omega) : Equiv.Perm ParkerLoop :=
  ⟨correction x, correction x, correction_involutive x, correction_involutive x⟩

theorem correction_sign (x : Omega) (s : ParkerBit) (b : ParkerLoop) :
    correction x (parkerSign s b) = parkerSign s (correction x b) := by
  simp [correction, parkerSign, add_comm, add_assoc]

theorem correction_omega (x : Omega) (b : ParkerLoop) :
    correction x (parkerLoopMultiply b parkerOmega) =
      parkerLoopMultiply (correction x b) (parkerSign 1 parkerOmega) := by
  unfold correction
  rw [parkerLoopMultiply_sign_right, parkerLoopMultiply_sign_left]
  change parkerSign (b.1.val x + 1) (parkerLoopMultiply b parkerOmega) = _
  simp only [parkerSign, Prod.mk.injEq, true_and]
  abel

def halfCorrection (x : Omega) : B1A2 ≃ₗ[ℝ] B3A2 :=
  firstSecond.transport thirdSecond (correctionEquiv x)
    (fun b => by
      change correction x (parkerLoopMultiply b (parkerSign 0 parkerOmega)) =
        parkerLoopMultiply (correction x b) (parkerSign 1 parkerOmega)
      rw [parkerSign_zero]
      exact correction_omega x b)
    (correction_sign x 1)

theorem halfCorrection_delta (x : Omega) (b : ParkerLoop) :
    halfCorrection x (delta2 b) = B3Axis2.delta (correction x b) :=
  firstSecond.transport_vector thirdSecond _ _ _ b

theorem halfCorrection_isometry (x : Omega) (v w : B1A2) :
    B3Axis2.form (halfCorrection x v) (halfCorrection x w) = secondAxisDomain.form v w := by
  let : Fintype firstSecond.geometry.pairing.Orbit := Fintype.ofFinite _
  exact firstSecond.transport_isometry thirdSecond _ _ _ v w

variable (M : Type*) [AddCommGroup M] [Module ℝ M]
def tensorCoordinates : NaturalSpace ⊗[ℝ] M ≃ₗ[ℝ] (Fin 24 → M) :=
  (TensorProduct.piLeft ℝ M (fun _ : Fin 24 => ℝ)).trans
    (LinearEquiv.piCongrRight fun _ => TensorProduct.lid ℝ M)

theorem tensorCoordinates_tmul (a : NaturalSpace) (v : M) (i : Fin 24) :
    tensorCoordinates M (a ⊗ₜ[ℝ] v) i = a i • v := rfl


variable {M}

def tensorComparison : TensorTwo ≃ₗ[ℝ] NaturalSpace ⊗[ℝ] B3A2 :=
  (tensorCoordinates B1A2).trans
    ((LinearEquiv.piCongrRight fun i => halfCorrection (coordinateMarking i)).trans
      (tensorCoordinates B3A2).symm)

theorem tensorComparison_coordinates (v : TensorTwo) (i : Fin 24) :
    tensorCoordinates B3A2 (tensorComparison v) i =
      halfCorrection (coordinateMarking i) (tensorCoordinates B1A2 v i) := by
  simp [tensorComparison]

theorem tensorComparison_point (x : Omega) (v : B1A2) :
    tensorComparison (pointVector x ⊗ₜ[ℝ] v) =
      pointVector x ⊗ₜ[ℝ] halfCorrection x v := by
  apply (tensorCoordinates B3A2).injective
  funext i
  rw [tensorComparison_coordinates, tensorCoordinates_tmul, tensorCoordinates_tmul, map_smul]
  by_cases hi : i = coordinateMarking.symm x
  · subst i
    simp
  · simp [pointVector, Pi.single_eq_of_ne hi]

theorem tensorComparison_delta (x : Omega) (b : ParkerLoop) :
    tensorComparison (pointVector x ⊗ₜ[ℝ] delta2 b) =
      pointVector x ⊗ₜ[ℝ] B3Axis2.delta (parkerSign (b.1.val x) b) := by
  rw [tensorComparison_point, halfCorrection_delta]
  rfl

open scoped BigOperators

private def coordinateForm (f : LinearMap.BilinForm ℝ M) : LinearMap.BilinForm ℝ (Fin 24 → M) :=
  ∑ i : Fin 24, f.compl₁₂ (LinearMap.proj i) (LinearMap.proj i)

theorem tensorCoordinates_form (f : LinearMap.BilinForm ℝ M)
    (v w : NaturalSpace ⊗[ℝ] M) :
    (naturalForm.tmul f) v w =
      ∑ i : Fin 24, f (tensorCoordinates M v i) (tensorCoordinates M w i) := by
  have he : naturalForm.tmul f =
      (coordinateForm f).compl₁₂ (tensorCoordinates M).toLinearMap
        (tensorCoordinates M).toLinearMap := by
    apply TensorProduct.ext'
    intro a v
    apply TensorProduct.ext'
    intro b w
    simp only [LinearMap.BilinForm.tensorDistrib_tmul, LinearMap.compl₁₂_apply,
      LinearEquiv.coe_coe, coordinateForm, LinearMap.sum_apply, LinearMap.proj_apply,
      tensorCoordinates_tmul, map_smul, LinearMap.smul_apply, smul_eq_mul]
    change f v w * (∑ i, a i * b i) = ∑ i, b i * (a i * f v w)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact congrArg (fun F : LinearMap.BilinForm ℝ (NaturalSpace ⊗[ℝ] M) => F v w) he

theorem tensorComparison_isometry (v w : TensorTwo) :
    (naturalForm.tmul B3Axis2.form) (tensorComparison v) (tensorComparison w) =
      (naturalForm.tmul secondAxisDomain.form) v w := by
  rw [tensorCoordinates_form, tensorCoordinates_form]
  apply Finset.sum_congr rfl
  intro i _
  rw [tensorComparison_coordinates v i, tensorComparison_coordinates w i]
  exact halfCorrection_isometry _ _ _


open SignedModules

/-- The comparison on the two actual natural halfspace modules in 29.7(1). -/
def sourceTensorComparison : Natural.B1_24 ⊗[ℝ] B1A2 ≃ₗ[ℝ] Natural.B3_24 ⊗[ℝ] B3A2 :=
  (TensorProduct.congr naturalLeechComparison (LinearEquiv.refl ℝ B1A2)).trans
    (tensorComparison.trans
      (TensorProduct.congr naturalLeechComparison.symm (LinearEquiv.refl ℝ B3A2)))

theorem sourceTensorComparison_delta (x : Omega) (b : ParkerLoop) :
    sourceTensorComparison (Natural.L 0 1 x ⊗ₜ[ℝ] delta2 b) =
      Natural.L 2 1 x ⊗ₜ[ℝ] B3Axis2.delta (parkerSign (b.1.val x) b) := by
  simp only [sourceTensorComparison, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply]
  rw [show naturalLeechComparison (Natural.L 0 1 x) = pointVector x from
    naturalLeechComparison_L_one x, tensorComparison_delta, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply]
  congr 1
  exact naturalLeechComparison.symm_apply_eq.mpr (naturalLeechComparison_L_one x).symm

end Sporadic.Monster.Construction.NMonomial.ZeroAction

module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.TensorComparison

/-!
# Marked tensor coordinates for the zero summands

Tensor distribution and the actual spin restriction identify the minus form
with its two half-spin product forms. Consequently the literal zero form is
the sum of its short and two tensor forms. `ModelSpace` publishes three marked
tensor slots; it carries no assumed group action. The first slot is intended
for the actual odd-family comparison, with the second and third slots left in
the existing coordinates of `Forms`.

An explicit odd-family isometry gives `zeroToModel`. Its generator and form
identities are proved here, to let the odd-family and full tensor-action
constructions proceed independently. The assembly owner must construct that
isometry with its stated generator formula, and construct the N-action with
its actual N1 compatibility, before using this transport for 29.8--29.9.

Source: Aschbacher, *Sporadic Groups*, 29.1(4), 29.7--29.9, pp. 154--158.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer
open Sporadic.Monster.Construction
open LocalC ShortFamilies TrialitySpin SpinActions
open scoped TensorProduct
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction

def tensorTwoForm : LinearMap.BilinForm ℝ TensorTwo := naturalForm.tmul secondAxisDomain.form
def tensorThreeForm : LinearMap.BilinForm ℝ TensorThree := naturalForm.tmul thirdAxisDomain.form

def tensorPairForm : LinearMap.BilinForm ℝ (TensorTwo × TensorThree) :=
  tensorTwoForm.compl₁₂ (LinearMap.fst ℝ _ _) (LinearMap.fst ℝ _ _) +
    tensorThreeForm.compl₁₂ (LinearMap.snd ℝ _ _) (LinearMap.snd ℝ _ _)

theorem tensorPairForm_apply (v w : TensorTwo × TensorThree) :
    tensorPairForm v w = tensorTwoForm v.1 w.1 + tensorThreeForm v.2 w.2 := rfl

theorem tensorSplitting_isometry (v w : MinusSpace) :
    tensorPairForm (tensorSplitting v) (tensorSplitting w) = minusForm v w := by
  have he : tensorPairForm.compl₁₂ tensorSplitting.toLinearMap tensorSplitting.toLinearMap =
      minusForm := by
    apply TensorProduct.ext'
    intro a s
    apply TensorProduct.ext'
    intro b t
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, tensorPairForm_apply,
      tensorSplitting_tmul, tensorTwoForm, tensorThreeForm, minusForm,
      LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul]
    rw [← add_mul, spinRestriction_isometry]
  exact congrArg (fun F : LinearMap.BilinForm ℝ MinusSpace => F v w) he

theorem zeroGamma_tensor_components (v w : ZeroSpace) :
    zeroGamma v w = shortForm sourceLatticeComparison v.1.val w.1.val +
      tensorTwoForm v.2.1 w.2.1 + tensorThreeForm v.2.2 w.2.2 := by
  rw [zeroGamma_components, ← tensorSplitting_isometry,
    tensorSplitting.apply_symm_apply, tensorSplitting.apply_symm_apply, tensorPairForm_apply]
  exact (add_assoc _ _ _).symm

/-- A marked tensor carrier for the first source summand, followed by the literal
second and third tensor summands. Its N-action still requires construction. -/
abbrev ModelSpace := TensorTwo × (TensorTwo × TensorThree)

def modelOdd (x : Omega) (b : ParkerLoop) : ModelSpace :=
  (pointVector x ⊗ₜ[ℝ] delta2 b,0)
def modelTwo (a : NaturalSpace) (s : B1A2) : ModelSpace := (0,a ⊗ₜ[ℝ] s,0)
def modelThree (a : NaturalSpace) (s : B1A3) : ModelSpace := (0,0,a ⊗ₜ[ℝ] s)

def modelGamma : LinearMap.BilinForm ℝ ModelSpace :=
  tensorTwoForm.compl₁₂ (LinearMap.fst ℝ _ _) (LinearMap.fst ℝ _ _) +
    tensorPairForm.compl₁₂ (LinearMap.snd ℝ _ _) (LinearMap.snd ℝ _ _)

theorem modelGamma_apply (v w : ModelSpace) : modelGamma v w =
    tensorTwoForm v.1 w.1 + tensorTwoForm v.2.1 w.2.1 + tensorThreeForm v.2.2 w.2.2 :=
  (add_assoc _ _ _).symm

/-- This transport awaits the genuine marked odd-family comparison of 29.8. -/
def zeroToModel (e : oddSpace ≃ₗ[ℝ] TensorTwo) : ZeroSpace ≃ₗ[ℝ] ModelSpace :=
  e.prodCongr (LinearEquiv.refl ℝ (TensorTwo × TensorThree))

theorem zeroToModel_two (e : oddSpace ≃ₗ[ℝ] TensorTwo) (a : NaturalSpace) (s : B1A2) :
    zeroToModel e (zeroTwo a s) = modelTwo a s := by
  simp [zeroToModel, zeroTwo, modelTwo]

theorem zeroToModel_three (e : oddSpace ≃ₗ[ℝ] TensorTwo) (a : NaturalSpace) (s : B1A3) :
    zeroToModel e (zeroThree a s) = modelThree a s := by
  simp [zeroToModel, zeroThree, modelThree]

theorem zeroToModel_odd (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (he : ∀ x b, e (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b)
    (x : Omega) (b : ParkerLoop) : zeroToModel e (zeroOdd x b) = modelOdd x b := by
  exact Prod.ext (he x b) rfl

theorem zeroToModel_isometry (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (he : ∀ v w : oddSpace, tensorTwoForm (e v) (e w) =
      shortForm sourceLatticeComparison v.val w.val) (v w : ZeroSpace) :
    modelGamma (zeroToModel e v) (zeroToModel e w) = zeroGamma v w := by
  rw [modelGamma_apply, zeroGamma_tensor_components]
  change tensorTwoForm (e v.1) (e w.1) + _ + _ = _
  rw [he]
  rfl

end Sporadic.Monster.Construction.NMonomial.ZeroAction

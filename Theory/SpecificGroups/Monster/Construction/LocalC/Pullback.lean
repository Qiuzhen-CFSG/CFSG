module
public import Theory.SpecificGroups.Monster.Construction.LocalC.Carrier
public import Theory.SpecificGroups.Monster.Construction.LocalC.RealLeech
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SpinQuotient

/-!
# The orthogonal spin–Leech pullback and its tensor image

The faithful spin action identifies an orthogonal normalizer element by its
linear map and the uniquely induced extraspecial automorphism. Take its
pullback with the full integral Leech isometry group over their actual
binary Leech actions, using the fixed source comparison. The tensor image
acts orthogonally on the natural–spin space; the pullback also acts on the
signed short vectors.

The tensor-image descent for the other summands is separate. This module
uses the orthogonal spin normalizer. Identifying it with the determinant-one
normalizer used in the source requires a separate theorem; it is not a
consequence of the definition or of the normalizer's recorded form law.

Source: Aschbacher, *Sporadic Groups*, Section 27, printed pp. 147–150.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct
open Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

/-- The orthogonal normalizer, recording its induced extraspecial automorphism. -/
def spinNormalizer : Subgroup ((SpinSpace ≃ₗ[ℝ] SpinSpace) × MulAut Q1Image) where
  carrier f := (∀ q v, f.1 (SpinAction.imageRepresentation q v) =
    SpinAction.imageRepresentation (f.2 q) (f.1 v)) ∧
    ∀ v w, bothAxesDomain.form (f.1 v) (f.1 w) = bothAxesDomain.form v w
  one_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  mul_mem' := by
    intro f g hf hg
    constructor
    · intro q v
      change f.1 (g.1 (SpinAction.imageRepresentation q v)) = _
      rw [hg.1, hf.1]
      rfl
    · intro v w
      change bothAxesDomain.form (f.1 (g.1 v)) (f.1 (g.1 w)) = _
      rw [hf.2, hg.2]
  inv_mem' := by
    intro f hf
    constructor
    · intro q v
      apply f.1.injective
      change f.1 (f.1.symm (SpinAction.imageRepresentation q v)) =
        f.1 (SpinAction.imageRepresentation (f.2.symm q) (f.1.symm v))
      rw [hf.1, f.1.apply_symm_apply, f.1.apply_symm_apply, f.2.apply_symm_apply]
    · intro v w
      change bothAxesDomain.form (f.1.symm v) (f.1.symm w) = _
      have h := hf.2 (f.1.symm v) (f.1.symm w)
      simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- The faithful spin action makes the recorded automorphism unique. -/
theorem spinNormalizer_ext {f g : spinNormalizer} (h : f.val.1 = g.val.1) : f = g := by
  apply Subtype.ext
  apply Prod.ext h
  apply MulEquiv.ext
  intro q
  apply SpinAction.imageRepresentation_faithful
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := f.val.1.surjective v
  rw [← f.prop.1, h, g.prop.1]

/-- Projection to the two actions being compared on the binary quotient. -/
def spinLeechProjection : spinNormalizer × LeechIsometryGroup →*
    MulAut Q1Image × LeechIsometryGroup where
  toFun p := (p.1.val.2, p.2)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The pullback over the actual action on the binary Leech space. -/
def localPullback : Subgroup (spinNormalizer × LeechIsometryGroup) :=
  (compatibleAutomorphisms sourceLatticeComparison).comap spinLeechProjection

/-- The extraspecial and Leech projections controlling the short vectors. -/
def pullbackCompatible : localPullback →* compatibleAutomorphisms sourceLatticeComparison where
  toFun p := ⟨(p.val.1.val.2,p.val.2),p.prop⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The natural-spin tensor action defining the local group. -/
def pullbackTensor : localPullback →* (MinusSpace ≃ₗ[ℝ] MinusSpace) where
  toFun p := TensorProduct.congr (realLeechRepresentation p.val.2) p.val.1.val.1
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.ext'
    intro v w
    simp
  map_mul' p q := by
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.ext'
    intro v w
    simp

@[simp] theorem pullbackTensor_tmul (p : localPullback) (a : NaturalSpace) (b : SpinSpace) :
    pullbackTensor p (a ⊗ₜ[ℝ] b) =
      realLeechRepresentation p.val.2 a ⊗ₜ[ℝ] p.val.1.val.1 b := rfl

theorem pullbackTensor_form (p : localPullback) (v w : MinusSpace) :
    minusForm (pullbackTensor p v) (pullbackTensor p w) = minusForm v w := by
  have h : minusForm.comp (pullbackTensor p).toLinearMap (pullbackTensor p).toLinearMap =
      minusForm := by
    apply TensorProduct.ext'
    intro a b
    apply TensorProduct.ext'
    intro c d
    simp only [LinearMap.BilinForm.comp_apply, LinearEquiv.coe_coe, pullbackTensor_tmul,
      minusForm_tmul, realLeechRepresentation_form, p.val.1.prop.2]
  exact congrArg (fun F : LinearMap.BilinForm ℝ MinusSpace => F v w) h

/-- The tensor image of the fixed spin–Leech pullback. -/
def C : Subgroup (MinusSpace ≃ₗ[ℝ] MinusSpace) := pullbackTensor.range

def pullbackToC : localPullback →* C := pullbackTensor.rangeRestrict

theorem pullbackToC_surjective : Function.Surjective pullbackToC :=
  pullbackTensor.rangeRestrict_surjective

theorem c_preserves_minusForm (g : C) (v w : MinusSpace) :
    minusForm (g.val v) (g.val w) = minusForm v w := by
  obtain ⟨p,rfl⟩ := pullbackToC_surjective g
  exact pullbackTensor_form p v w

/-- The signed short-vector action before descent to the tensor image. -/
def pullbackShort : Representation ℝ localPullback BShort :=
  (shortAction sourceLatticeComparison).comp pullbackCompatible

theorem pullbackShort_form (p : localPullback) (v w : BShort) :
    shortForm sourceLatticeComparison (pullbackShort p v) (pullbackShort p w) =
      shortForm sourceLatticeComparison v w :=
  shortAction_form sourceLatticeComparison (pullbackCompatible p) v w

end Sporadic.Monster.Construction.LocalC

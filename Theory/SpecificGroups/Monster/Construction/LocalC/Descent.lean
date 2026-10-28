module
public import Theory.SpecificGroups.Monster.Construction.LocalC.Pullback

/-!
# Descent of the short and symmetric actions to the tensor image

Conjugating spin operators by a tensor-kernel element, then contracting
with one natural coordinate, shows that its extraspecial automorphism is
trivial. The fixed lattice comparison makes its binary Leech action
trivial, so the proved Leech kernel theorem kills its symmetric action too.
The first isomorphism theorem descends both actions to the tensor image.
Their orthogonal sum with its defining tensor action is faithful and
preserves the explicit positive form on the fixed Griess carrier.

This proves descent, not the separate identification of the orthogonal
normalizer with the determinant-one normalizer in the source.

Source: Aschbacher, *Sporadic Groups*, Section 27, printed pp. 148–150.
-/

public section
noncomputable section
open scoped TensorProduct
open Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

/-- Contract a tensor with the first natural coordinate. -/
def firstContraction : MinusSpace →ₗ[ℝ] SpinSpace :=
  (TensorProduct.lid ℝ SpinSpace).toLinearMap.comp
    (TensorProduct.map (LinearMap.proj (0 : Fin 24)) (LinearMap.id : SpinSpace →ₗ[ℝ] SpinSpace))

theorem firstContraction_tmul (v : NaturalSpace) (s : SpinSpace) :
    firstContraction (v ⊗ₜ[ℝ] s) = v 0 • s := by rfl

/-- An element killed on tensors induces the identity extraspecial automorphism. -/
theorem pullbackTensor_kernel_automorphism (p : localPullback) (hp : pullbackTensor p = 1)
    (q : Q1Image) : p.val.1.val.2 q = q := by
  apply SpinAction.imageRepresentation_faithful
  apply LinearMap.ext
  intro s
  have h (a : NaturalSpace) (b : SpinSpace) :
      pullbackTensor p (a ⊗ₜ[ℝ] SpinAction.imageRepresentation q b) =
        TensorProduct.map (LinearMap.id : NaturalSpace →ₗ[ℝ] NaturalSpace)
          (SpinAction.imageRepresentation (p.val.1.val.2 q))
          (pullbackTensor p (a ⊗ₜ[ℝ] b)) := by
    rw [pullbackTensor_tmul, pullbackTensor_tmul, TensorProduct.map_tmul]
    change _ = _ ⊗ₜ[ℝ] _
    rw [p.val.1.prop.1]
    rfl
  have he := h (Pi.single 0 1) s
  rw [hp] at he
  change Pi.single 0 1 ⊗ₜ[ℝ] SpinAction.imageRepresentation q s =
    TensorProduct.map (LinearMap.id : NaturalSpace →ₗ[ℝ] NaturalSpace)
      (SpinAction.imageRepresentation (p.val.1.val.2 q)) (Pi.single 0 1 ⊗ₜ[ℝ] s) at he
  rw [TensorProduct.map_tmul] at he
  have hc := congrArg firstContraction he
  simpa only [firstContraction_tmul, LinearMap.id_apply, Pi.single_eq_same, one_smul] using hc.symm

/-- Tensor-kernel elements act trivially on the actual binary Leech space. -/
theorem pullbackTensor_kernel_modTwo (p : localPullback) (hp : pullbackTensor p = 1) :
    leechModTwoRepresentation p.val.2 = 1 := by
  apply DFunLike.ext
  intro x
  obtain ⟨q,rfl⟩ := latticeClass_surjective sourceLatticeComparison x
  have h := p.prop q
  change latticeClass sourceLatticeComparison (p.val.1.val.2 q) = _ at h
  rw [pullbackTensor_kernel_automorphism p hp] at h
  exact h.symm

/-- The signed conjugation action is constant on fibers of the tensor map. -/
theorem pullbackToC_kernel_le_short : pullbackToC.ker ≤ pullbackShort.ker := by
  intro p hp
  apply (shortAction_kernel_iff sourceLatticeComparison (pullbackCompatible p)).mpr
  intro q
  exact pullbackTensor_kernel_automorphism p (congrArg Subtype.val hp) q.val

/-- The symmetric tensor action of the actual lattice factor. -/
@[expose] def pullbackSymmetric : Representation ℝ localPullback SymmetricPart where
  toFun p := (symmetricLeechRepresentation p.val.2).toLinearMap
  map_one' := by rw [show (1 : localPullback).val.2 = 1 from rfl, map_one]; rfl
  map_mul' p q := by
    change (symmetricLeechRepresentation (p.val.2 * q.val.2)).toLinearMap = _
    rw [map_mul]
    rfl

/-- The symmetric action is constant on fibers too, by the proved Leech kernels. -/
theorem pullbackToC_kernel_le_symmetric : pullbackToC.ker ≤ pullbackSymmetric.ker := by
  intro p hp
  have h := pullbackTensor_kernel_modTwo p (congrArg Subtype.val hp)
  have hs := (symmetricLeechRepresentation_kernel p.val.2).mpr
    ((leechModTwoRepresentation_kernel p.val.2).mp h)
  change (symmetricLeechRepresentation p.val.2).toLinearMap = 1
  rw [hs]
  rfl

/-- The first isomorphism theorem for the fixed tensor image. -/
def tensorImageEquiv : (localPullback ⧸ pullbackTensor.ker) ≃* C :=
  QuotientGroup.quotientKerEquivRange pullbackTensor

theorem tensorImageEquiv_mk (p : localPullback) :
    tensorImageEquiv (QuotientGroup.mk' pullbackTensor.ker p) = pullbackToC p := by rfl

theorem tensorImageEquiv_symm_pullback (p : localPullback) :
    tensorImageEquiv.symm (pullbackToC p) = QuotientGroup.mk' pullbackTensor.ker p :=
  tensorImageEquiv.symm_apply_apply (QuotientGroup.mk' pullbackTensor.ker p)

/-- Descent through the tensor image, using the first isomorphism theorem. -/
def tensorDescend {M : Type*} [Monoid M] (ρ : localPullback →* M)
    (hρ : pullbackToC.ker ≤ ρ.ker) : C →* M :=
  (QuotientGroup.lift pullbackTensor.ker ρ (fun _ hp => hρ (Subtype.ext hp))).comp
      tensorImageEquiv.symm.toMonoidHom

theorem tensorDescend_pullback {M : Type*} [Monoid M] (ρ : localPullback →* M)
    (hρ : pullbackToC.ker ≤ ρ.ker) (p : localPullback) :
    tensorDescend ρ hρ (pullbackToC p) = ρ p := by
  change (QuotientGroup.lift pullbackTensor.ker ρ (fun _ hp => hρ (Subtype.ext hp)))
    (tensorImageEquiv.symm (pullbackToC p)) = _
  rw [tensorImageEquiv_symm_pullback]
  rfl

/-- The descended short-extraspecial representation on the fixed source carrier. -/
def cShort : Representation ℝ C BShort :=
  tensorDescend pullbackShort pullbackToC_kernel_le_short

@[simp] theorem cShort_pullback (p : localPullback) : cShort (pullbackToC p) = pullbackShort p :=
  tensorDescend_pullback _ _ p

/-- The descended symmetric-square representation. -/
def cSymmetric : Representation ℝ C SymmetricPart :=
  tensorDescend pullbackSymmetric pullbackToC_kernel_le_symmetric

@[simp] theorem cSymmetric_pullback (p : localPullback) :
    cSymmetric (pullbackToC p) = pullbackSymmetric p :=
  tensorDescend_pullback _ _ p

theorem cShort_form (g : C) (v w : BShort) :
    shortForm sourceLatticeComparison (cShort g v) (cShort g w) =
      shortForm sourceLatticeComparison v w := by
  obtain ⟨p,rfl⟩ := pullbackToC_surjective g
  rw [cShort_pullback]
  exact pullbackShort_form p v w

theorem cSymmetric_form (g : C) (v w : SymmetricPart) :
    symmetricGamma (cSymmetric g v) (cSymmetric g w) = symmetricGamma v w := by
  obtain ⟨p,rfl⟩ := pullbackToC_surjective g
  rw [cSymmetric_pullback]
  exact symmetricLeechRepresentation_form p.val.2 v w

/-- The orthogonal action on the fixed Griess carrier. -/
def cRepresentation : Representation ℝ C B where
  toFun g := blockMap sourceLatticeComparison g.val.toLinearMap (cShort g) (cSymmetric g)
  map_one' := by
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    rw [map_mul, map_mul]
    rfl

theorem cRepresentation_apply (g : C) (v : B) :
    cRepresentation g v = (g.val v.1, cShort g v.2.1, cSymmetric g v.2.2) := by rfl

theorem cRepresentation_form (g : C) (v w : B) :
    fixedGamma (cRepresentation g v) (cRepresentation g w) = fixedGamma v w :=
  blockMap_preserves_gamma sourceLatticeComparison _ _ _ (c_preserves_minusForm g)
    (cShort_form g) (cSymmetric_form g) v w

/-- Faithfulness already follows from the tensor-image action on the first summand. -/
theorem cRepresentation_faithful : Function.Injective cRepresentation := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun f : Module.End ℝ B => (f (v,0,0)).1) he

end Sporadic.Monster.Construction.LocalC

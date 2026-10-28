module

public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadKernels
public import Theory.Mathieu.M24.ChapterHStabilizers.OctadAction

/-!
# Restriction of the octad four-space to the native hexad stabilizers

The actual inner and outer hexad kernels inherit the moment coordinates of
the octad transvection axis through their literal embeddings in M24. Their
conjugation actions are restrictions of the proved octad linear action.
The kernels are precisely the intrinsic two-cores, so these actions descend
faithfully through the existing six-coordinate A6 and S6 markings.

This is the restriction step in Aschbacher--Smith H.14.3(3), printed p.397.
The identification of the resulting four-space with the natural S6 module
requires a further invariant-form comparison; faithfulness alone is not
asserted to establish that identification here.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open Sporadic.Mathieu.M24ChapterHStabilizers
open MathieuCode.Hexad.CocodeAction.SixPointModel
namespace Sporadic.Mathieu.M22ChapterH.Hexad.Action
noncomputable section

abbrev Space := OctadAction.Space
abbrev Inner := m22InnerHexadStabilizer O
abbrev Outer := m22OuterHexadStabilizer O

/-- The actual inclusion of the inner stabilizer in the pair stabilizer. -/
def innerToOuter : Inner →* Outer where
  toFun g := ⟨m22ToPairStabilizer g.val, g.property⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- The octad moment coordinates on the native M22 kernel. -/
def innerCoordinates : m22InnerHexadKernel O ≃* Multiplicative Space :=
  innerKernelOctadEquiv.trans (OctadAction.pointwiseCoordinates O)

/-- The same moment coordinates on the kernel in the literal pair overgroup. -/
def outerCoordinates : m22OuterHexadKernel O ≃* Multiplicative Space :=
  outerKernelOctadEquiv.trans (OctadAction.pointwiseCoordinates O)

/-- The two kernel markings agree under the original M22 embedding. -/
def kernelToOuter : m22InnerHexadKernel O ≃* m22OuterHexadKernel O :=
  innerKernelOctadEquiv.trans outerKernelOctadEquiv.symm

theorem kernelToOuter_coe (a : m22InnerHexadKernel O) :
    (kernelToOuter a).val = m22ToPairStabilizer a.val := by
  apply Subtype.ext
  change (outerKernelOctadEquiv (kernelToOuter a)).val = (innerKernelOctadEquiv a).val
  exact congrArg Subtype.val (outerKernelOctadEquiv.apply_symm_apply (innerKernelOctadEquiv a))

theorem coordinates_compatible (a : m22InnerHexadKernel O) :
    outerCoordinates (kernelToOuter a) = innerCoordinates a := by
  exact congrArg (OctadAction.pointwiseCoordinates O)
    (outerKernelOctadEquiv.apply_symm_apply (innerKernelOctadEquiv a))

/-- The actual restricted octad action of the inner hexad stabilizer. -/
def innerLinearAction : Inner →* (Space ≃ₗ[ZMod 2] Space) :=
  (OctadAction.linearAction O).comp (octadHom m22ToPairStabilizer)

/-- The actual restricted octad action of the outer hexad stabilizer. -/
def outerLinearAction : Outer →* (Space ≃ₗ[ZMod 2] Space) :=
  (OctadAction.linearAction O).comp (octadHom (MonoidHom.id m22PairStabilizer))

theorem linearAction_compatible (g : Inner) :
    outerLinearAction (innerToOuter g) = innerLinearAction g := rfl

private theorem pointwise_symm_conjugation (g : octadStabilizer O) (v : Space) :
    g.val * ((OctadAction.pointwiseCoordinates O).symm (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      ((OctadAction.pointwiseCoordinates O).symm
        (Multiplicative.ofAdd (OctadAction.linearAction O g v))).val := by
  have h := OctadAction.pointwiseCoordinates_conjugation O g
    ((OctadAction.pointwiseCoordinates O).symm (Multiplicative.ofAdd v))
  rw [MulEquiv.apply_symm_apply] at h
  have he := (OctadAction.pointwiseCoordinates O).symm_apply_apply
    (CocodeOctad.Dynamics.kernelConjugate O g
      ((OctadAction.pointwiseCoordinates O).symm (Multiplicative.ofAdd v)))
  have hm := Multiplicative.toAdd.injective h
  rw [hm] at he
  exact (congrArg Subtype.val he).symm

private theorem innerCoordinates_symm_coe (v : Space) :
    m22Embedding ((innerCoordinates.symm (Multiplicative.ofAdd v)).val) =
      ((OctadAction.pointwiseCoordinates O).symm (Multiplicative.ofAdd v)).val := by
  exact congrArg Subtype.val
    (innerKernelOctadEquiv.apply_symm_apply ((OctadAction.pointwiseCoordinates O).symm _))

private theorem outerCoordinates_symm_coe (v : Space) :
    (outerCoordinates.symm (Multiplicative.ofAdd v)).val.val =
      ((OctadAction.pointwiseCoordinates O).symm (Multiplicative.ofAdd v)).val := by
  exact congrArg Subtype.val
    (outerKernelOctadEquiv.apply_symm_apply ((OctadAction.pointwiseCoordinates O).symm _))

/-- Conjugation in native M22, in the inherited four binary coordinates. -/
theorem innerCoordinates_conjugation (g : Inner) (v : Space) :
    g.val * (innerCoordinates.symm (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      (innerCoordinates.symm (Multiplicative.ofAdd (innerLinearAction g v))).val := by
  apply m22Embedding_injective
  rw [map_mul, map_mul, map_inv, innerCoordinates_symm_coe, innerCoordinates_symm_coe]
  exact pointwise_symm_conjugation (octadHom m22ToPairStabilizer g) v

/-- Conjugation in the literal pair overgroup, in the same coordinates. -/
theorem outerCoordinates_conjugation (g : Outer) (v : Space) :
    g.val * (outerCoordinates.symm (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      (outerCoordinates.symm (Multiplicative.ofAdd (outerLinearAction g v))).val := by
  apply Subtype.ext
  change g.val.val * (outerCoordinates.symm (Multiplicative.ofAdd v)).val.val * g.val.val⁻¹ = _
  rw [outerCoordinates_symm_coe, outerCoordinates_symm_coe]
  exact pointwise_symm_conjugation (octadHom (MonoidHom.id m22PairStabilizer) g) v

private theorem octad_action_eq_one (g : octadStabilizer O) :
    OctadAction.linearAction O g = 1 ↔ g.val ∈ octadPointwiseKernel O := by
  rw [← MonoidHom.mem_ker, OctadAction.linearAction_ker, OctadAction.Core,
    CocodeOctad.core_eq_coordinateKernel, CocodeOctad.mem_coordinateAction_ker,
    mem_octadPointwiseKernel]

/-- Exact kernel inside the inner stabilizer. -/
theorem innerLinearAction_ker : innerLinearAction.ker = pCore 2 Inner := by
  rw [← inner_kernel_eq_core, innerCoordinateAction_ker inner_kernel_image]
  ext g
  change OctadAction.linearAction O (octadHom m22ToPairStabilizer g) = 1 ↔
    g.val ∈ m22InnerHexadKernel O
  rw [octad_action_eq_one]
  change m22Embedding g.val ∈ octadPointwiseKernel O ↔ _
  rw [← inner_kernel_image]
  constructor
  · rintro ⟨a, ha, he⟩
    exact m22Embedding_injective he ▸ ha
  · intro hg
    exact ⟨g.val, hg, rfl⟩

/-- Exact kernel inside the outer stabilizer. -/
theorem outerLinearAction_ker : outerLinearAction.ker = pCore 2 Outer := by
  rw [← outer_kernel_eq_core, outerCoordinateAction_ker outer_kernel_image]
  ext g
  change OctadAction.linearAction O (octadHom (MonoidHom.id m22PairStabilizer) g) = 1 ↔
    g.val ∈ m22OuterHexadKernel O
  rw [octad_action_eq_one]
  change g.val.val ∈ octadPointwiseKernel O ↔ _
  rw [← outer_kernel_image]
  constructor
  · rintro ⟨a, ha, he⟩
    exact (Subtype.ext he : a = g.val) ▸ ha
  · intro hg
    exact ⟨g.val, hg, rfl⟩

/-- Faithful descent on the original inner intrinsic quotient. -/
def innerQuotientAction : (Inner ⧸ pCore 2 Inner) →* (Space ≃ₗ[ZMod 2] Space) :=
  QuotientGroup.lift _ innerLinearAction innerLinearAction_ker.symm.le

/-- Faithful descent on the original outer intrinsic quotient. -/
def outerQuotientAction : (Outer ⧸ pCore 2 Outer) →* (Space ≃ₗ[ZMod 2] Space) :=
  QuotientGroup.lift _ outerLinearAction outerLinearAction_ker.symm.le

theorem innerQuotientAction_injective : Function.Injective innerQuotientAction :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr innerLinearAction_ker.symm

theorem outerQuotientAction_injective : Function.Injective outerQuotientAction :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr outerLinearAction_ker.symm

/-- A6 on the actual six coordinates, acting on the inherited octad four-space. -/
def alternatingAction : alternatingGroup H →* (Space ≃ₗ[ZMod 2] Space) :=
  innerQuotientAction.comp innerQuotientEquiv.symm.toMonoidHom

/-- S6 on the actual six coordinates, acting on the inherited octad four-space.
This marking has not been changed by an exceptional automorphism. -/
def symmetricAction : Equiv.Perm H →* (Space ≃ₗ[ZMod 2] Space) :=
  outerQuotientAction.comp outerQuotientEquiv.symm.toMonoidHom

theorem alternatingAction_injective : Function.Injective alternatingAction :=
  innerQuotientAction_injective.comp innerQuotientEquiv.symm.injective

theorem symmetricAction_injective : Function.Injective symmetricAction :=
  outerQuotientAction_injective.comp outerQuotientEquiv.symm.injective

@[simp] theorem alternatingAction_mk (g : Inner) :
    alternatingAction (innerQuotientEquiv (QuotientGroup.mk g)) = innerLinearAction g := by
  change innerQuotientAction (innerQuotientEquiv.symm (innerQuotientEquiv _)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

@[simp] theorem symmetricAction_coordinate (g : Outer) :
    symmetricAction (outerCoordinateAction g) = outerLinearAction g := by
  rw [← outerQuotientEquiv_mk]
  change outerQuotientAction (outerQuotientEquiv.symm (outerQuotientEquiv _)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The inner and outer descended actions retain the same six-coordinate marking. -/
theorem symmetricAction_alternating (g : alternatingGroup H) :
    symmetricAction g.val = alternatingAction g := by
  obtain ⟨q, rfl⟩ := innerQuotientEquiv.surjective g
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Inner) q
  change symmetricAction (innerQuotientEquiv (QuotientGroup.mk a)).val =
    alternatingAction (innerQuotientEquiv (QuotientGroup.mk a))
  rw [alternatingAction_mk, innerQuotientEquiv_mk]
  change symmetricAction (outerCoordinateAction (innerToOuter a)) = innerLinearAction a
  rw [symmetricAction_coordinate, linearAction_compatible]

end
end Sporadic.Mathieu.M22ChapterH.Hexad.Action

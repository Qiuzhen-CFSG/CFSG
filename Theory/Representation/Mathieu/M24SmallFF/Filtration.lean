module

public import Theory.Representation.Mathieu.M24SmallFF.ZeroMaps
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# The literal Golay filtration and its tensor maps

The maps here are the actual inclusions and quotient maps in
`1 < Golay < Core < Full`. Their successive quotients are the native code,
cocode and trivial module. Right exactness of tensor product transfers
zero-map obstructions along each of these exact sequences.

Source: Aschbacher–Smith, H.13.1; this retains the native permutation action
and the literal Golay quotient conventions used by the B.4 consumer.
-/

open Representation
open scoped TensorProduct
namespace Representation.Mathieu.M24SmallFF
@[expose] public noncomputable section
section Generic
variable {k G U W X V Y : Type*} [Field k] [Group G]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X] [AddCommGroup V] [Module k V]
  [AddCommGroup Y] [Module k Y]
  {α : Representation k G U} {β : Representation k G W} {γ : Representation k G X}
  {ρ : Representation k G V}
lemma extension_maps_zero (i:α.IntertwiningMap β) (q:β.IntertwiningMap γ)
    (hq:Function.Surjective q) (hex:q.toLinearMap.ker=i.toLinearMap.range)
    (hi:∀f:α.IntertwiningMap ρ,f=0) (hγ:∀f:γ.IntertwiningMap ρ,f=0)
    (f:β.IntertwiningMap ρ) : f=0 := by
  apply map_eq_zero_of_ker q hq hγ f
  intro w hw
  rw [hex] at hw
  obtain ⟨u,rfl⟩ := hw
  exact congrArg (fun e:α.IntertwiningMap ρ=>e u) (hi (f.comp i))
lemma tensor_extension_maps_zero (i:α.IntertwiningMap β) (q:β.IntertwiningMap γ)
    (hq:Function.Surjective q) (hex:q.toLinearMap.ker=i.toLinearMap.range)
    (τ:Representation k G Y)
    (hi:∀f:(α.tprod τ).IntertwiningMap ρ,f=0)
    (hγ:∀f:(γ.tprod τ).IntertwiningMap ρ,f=0)
    (f:(β.tprod τ).IntertwiningMap ρ) : f=0 := by
  apply extension_maps_zero (i.rTensor τ) (q.rTensor τ)
    (LinearMap.rTensor_surjective Y hq) _ hi hγ f
  exact (_root_.rTensor_exact Y
    (LinearMap.exact_iff.mpr hex) hq).linearMap_ker_eq
end Generic
open Sporadic.Mathieu MathieuCode
abbrev oneRep := Representation.trivial (ZMod 2) M24 (ZMod 2)
def lineToGolay : oneRep.IntertwiningMap golayRepresentation where
  toLinearMap := (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2).smulRight
    ⟨BinaryPermutation.allOne (Fin 24),constants_le_golay (Submodule.subset_span (by simp))⟩
  isIntertwining' g := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    rfl
def golayToCode : golayRepresentation.IntertwiningMap codeRepresentation :=
  ⟨codeLine.mkQ,fun _=>rfl⟩
lemma golayToCode_surjective : Function.Surjective golayToCode := codeLine.mkQ_surjective
lemma golayToCode_exact : golayToCode.toLinearMap.ker=lineToGolay.toLinearMap.range := by
  ext v
  change codeLine.mkQ v=0 ↔ ∃c,lineToGolay c=v
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change v.val∈BinaryPermutation.constants (Fin 24) ↔ _
  rw [BinaryPermutation.constants,Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c,hc⟩
    exact ⟨c,Subtype.ext hc⟩
  · rintro ⟨c,hc⟩
    exact ⟨c,congrArg Subtype.val hc⟩
def golayToCore : golayRepresentation.IntertwiningMap coreRepresentation where
  toLinearMap := golay.inclusion golay_le_core
  isIntertwining' _ := rfl
def coreToCocode : coreRepresentation.IntertwiningMap cocodeRepresentation :=
  ⟨codeInCore.mkQ,fun _=>rfl⟩
lemma coreToCocode_surjective : Function.Surjective coreToCocode := codeInCore.mkQ_surjective
lemma coreToCocode_exact : coreToCocode.toLinearMap.ker=golayToCore.toLinearMap.range := by
  ext v
  change codeInCore.mkQ v=0 ↔ ∃w,golayToCore w=v
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hv
    exact ⟨⟨v.val,hv⟩,rfl⟩
  · rintro ⟨w,rfl⟩
    exact w.property
def coreToFull : coreRepresentation.IntertwiningMap fullRepresentation :=
  ⟨Core.subtype,fun _=>rfl⟩
def fullToOne : fullRepresentation.IntertwiningMap oneRep where
  toLinearMap := BinaryPermutation.augmentation (Fin 24)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact BinaryPermutation.augmentation_permute (Fin 24) g.val v
lemma fullToOne_surjective : Function.Surjective fullToOne := by
  intro c
  refine ⟨Pi.single 0 c,?_⟩
  change ∑i:Fin 24,Pi.single 0 c i=c
  simp
lemma fullToOne_exact : fullToOne.toLinearMap.ker=coreToFull.toLinearMap.range := by
  exact Core.range_subtype.symm
section Consumers
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) M24 V)
lemma full_maps_zero_of_constituents
    (h1 : ∀ f : oneRep.IntertwiningMap ρ, f = 0)
    (hc : ∀ f : codeRepresentation.IntertwiningMap ρ, f = 0)
    (hd : ∀ f : cocodeRepresentation.IntertwiningMap ρ, f = 0)
    (f : fullRepresentation.IntertwiningMap ρ) : f = 0 := by
  have hg := extension_maps_zero lineToGolay golayToCode golayToCode_surjective
    golayToCode_exact h1 hc
  have hk := extension_maps_zero golayToCore coreToCocode coreToCocode_surjective
    coreToCocode_exact hg hd
  exact extension_maps_zero coreToFull fullToOne fullToOne_surjective fullToOne_exact hk h1 f
lemma full_tensor_maps_zero_of_constituents (τ : Representation (ZMod 2) M24 W)
    (h1 : ∀ f : (oneRep.tprod τ).IntertwiningMap ρ, f = 0)
    (hc : ∀ f : (codeRepresentation.tprod τ).IntertwiningMap ρ, f = 0)
    (hd : ∀ f : (cocodeRepresentation.tprod τ).IntertwiningMap ρ, f = 0)
    (f : (fullRepresentation.tprod τ).IntertwiningMap ρ) : f = 0 := by
  have hg := tensor_extension_maps_zero lineToGolay golayToCode golayToCode_surjective
    golayToCode_exact τ h1 hc
  have hk := tensor_extension_maps_zero golayToCore coreToCocode coreToCocode_surjective
    coreToCocode_exact τ hg hd
  exact tensor_extension_maps_zero coreToFull fullToOne fullToOne_surjective
    fullToOne_exact τ hk h1 f
end Consumers

end
end Representation.Mathieu.M24SmallFF

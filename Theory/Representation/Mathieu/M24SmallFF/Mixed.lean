module

public import Theory.Representation.Mathieu.M24SmallFF.ZeroMaps
public import Theory.Representation.Mathieu.M24SmallFF.TensorSquare
public import Theory.Representation.BinaryOffender.NormalizerConjugateDimension

/-!
# The native code tensor factors have no maps to a small FF target

The mixed tensor is equivariantly the endomorphism space of the native code.
Its trace kernel is the actual simple degree-120 module; the scalar identity
is fixed, so both parts map to zero in a small faithful irreducible target.
The square tensors are handled by their alternating and diagonal maps.

This uses only the proved small native models and the literal code/cocode
no-FF theorems, without a classification of the full M24 degree spectrum.
Source: Aschbacher–Smith, H.13–H.16 and K.4.
-/

open Representation
open scoped TensorProduct
namespace Representation.Mathieu.M24SmallFF
@[expose] public noncomputable section
section Generic
variable {k G U W V : Type*} [Field k] [Group G]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  [AddCommGroup V] [Module k V]
  {τ : Representation k G U} {σ : Representation k G W} {ρ : Representation k G V}
lemma map_zero_of_equiv (E : τ.Equiv σ)
    (hz : ∀f:σ.IntertwiningMap ρ,f=0) (f:τ.IntertwiningMap ρ) : f=0 := by
  have hh := hz (f.comp E.symm.toIntertwiningMap)
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  have hu := congrArg (fun q:σ.IntertwiningMap ρ => q (E u)) hh
  change f (E.symm (E u))=0 at hu
  rw [E.symm_apply_apply] at hu
  exact hu

def tensorLeftEquiv (E:τ.Equiv σ) (υ:Representation k G V) :
    (τ.tprod υ).Equiv (σ.tprod υ) :=
  (E.toIntertwiningMap.rTensor υ).ofBijective
    (_root_.TensorProduct.congr E.toLinearEquiv (LinearEquiv.refl k V)).bijective
end Generic
open Sporadic.Mathieu MathieuCode BinaryOffender
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) M24 V) [ρ.IsIrreducible]
    (hf:Function.Injective ρ) (hff:IsFFModule ρ) (hd:Module.finrank (ZMod 2) V≤24)
omit [FiniteDimensional (ZMod 2) V] in
include hf in
lemma fixed_vector_zero (v:V) (hv:∀g,ρ g v=v) : v=0 := by
  let : Nontrivial M24 := Finite.one_lt_card_iff_nontrivial.mp (by rw [m24_order]; decide)
  have hh : v∈ρ.invariants := hv
  rw [invariants_eq_bot_of_faithful_irreducible ρ hf inferInstance] at hh
  exact hh
omit [FiniteDimensional (ZMod 2) V] in
include hf in
lemma trivial_map_zero (f:(Representation.trivial (ZMod 2) M24 (ZMod 2)).IntertwiningMap ρ) : f=0 := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  apply fixed_vector_zero ρ hf
  intro g
  exact (LinearMap.congr_fun (f.isIntertwining' g) c).symm
include hf hd in
lemma endomorphism_map_zero (f:(codeRepresentation.linHom codeRepresentation).IntertwiningMap ρ) : f=0 := by
  let i : Native120.nativeTraceZeroRepresentation.IntertwiningMap
      (codeRepresentation.linHom codeRepresentation) :=
    ⟨Native120.nativeTraceZero.toSubmodule.subtype,fun _=>rfl⟩
  have hi := traceZero_map_zero ρ hd (f.comp i)
  have hid : f (1:Module.End (ZMod 2) Code)=0 := by
    apply fixed_vector_zero ρ hf
    intro g
    have hh := LinearMap.congr_fun (f.isIntertwining' g) (1:Module.End (ZMod 2) Code)
    have he : (codeRepresentation.linHom codeRepresentation) g 1=1 := by
      change codeRepresentation g * 1 * codeRepresentation g⁻¹=1
      rw [mul_one, ←map_mul, mul_inv_cancel, map_one]
    change f ((codeRepresentation.linHom codeRepresentation) g 1) = ρ g (f 1) at hh
    rw [he] at hh
    exact hh.symm
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  let c := LinearMap.trace (ZMod 2) Code x
  have hy : x-c•(1:Module.End (ZMod 2) Code)∈Native120.nativeTraceZero.toSubmodule := by
    change LinearMap.trace (ZMod 2) Code (x-c•(1:Module.End (ZMod 2) Code))=0
    rw [map_sub,map_smul,LinearMap.trace_one,finrank_code]
    rw [show ((11 : ℕ) : ZMod 2) = 1 from by decide, smul_eq_mul, mul_one]
    exact sub_self _
  have hz := congrArg (fun q:Native120.nativeTraceZeroRepresentation.IntertwiningMap ρ =>
      q ⟨x-c•(1:Module.End (ZMod 2) Code),hy⟩) hi
  change f (x-c•(1:Module.End (ZMod 2) Code))=0 at hz
  change f x = 0
  simpa only [map_sub,map_smul,hid,smul_zero,sub_zero] using hz
include hf hd in
lemma cocode_code_map_zero (f:(cocodeRepresentation.tprod codeRepresentation).IntertwiningMap ρ) : f=0 := by
  let C := tensorLeftEquiv cocodeDuality codeRepresentation
  let E := Representation.Equiv.dualTensorHom codeRepresentation codeRepresentation
  have hh := endomorphism_map_zero ρ hf hd
    ((f.comp C.symm.toIntertwiningMap).comp E.symm.toIntertwiningMap)
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  have hu := congrArg (fun q:(codeRepresentation.linHom codeRepresentation).IntertwiningMap ρ => q (E (C u))) hh
  change f (C.symm (E.symm (E (C u)))) = 0 at hu
  rw [E.symm_apply_apply, C.symm_apply_apply] at hu
  exact hu
include hf hd in
lemma code_cocode_map_zero (f:(codeRepresentation.tprod cocodeRepresentation).IntertwiningMap ρ) : f=0 := by
  exact map_zero_of_equiv (Representation.TensorProduct.comm _ _) (cocode_code_map_zero ρ hf hd) f
include hff hd in
lemma code_code_map_zero (f:(codeRepresentation.tprod codeRepresentation).IntertwiningMap ρ) : f=0 :=
  tensorSquare_map_zero _ _ (code_map_zero ρ hff) (codeExterior_map_zero ρ hff hd) f
include hff hd in
lemma cocode_cocode_map_zero (f:(cocodeRepresentation.tprod cocodeRepresentation).IntertwiningMap ρ) : f=0 :=
  tensorSquare_map_zero _ _ (cocode_map_zero ρ hff) (cocodeExterior_map_zero ρ hff hd) f
end
end Representation.Mathieu.M24SmallFF

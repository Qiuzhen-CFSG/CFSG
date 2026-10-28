module
public import Theory.PGroupCore
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Data.ZMod.Basic
/-!
# Faithful binary restriction across two fixed layers

For a faithful binary representation, the kernel on an invariant subspace
containing every displacement has exponent at most two. It therefore lies
in the two-core. A trivial two-core makes the restriction faithful; this
also applies to a normal subgroup of an ambient group with trivial two-core.
The dual of the same action remains faithful. No irreducibility or splitting
of a central layer is needed.

Source: the two-layer argument in Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup
namespace Representation
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
theorem two_layer_kernel_isTwoGroup (ρ : Representation (ZMod 2) H W)
    (J : Subrepresentation ρ) (hf : Function.Injective ρ)
    (hd : ∀ g w, ρ g w - w ∈ J) : IsPGroup 2 J.toRepresentation.ker := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply hf
  ext w
  have he := LinearMap.congr_fun (MonoidHom.mem_ker.mp x.property)
    (⟨ρ x w - w, hd x w⟩ : J.toSubmodule)
  have he' := congrArg Subtype.val he
  change ρ x (ρ x w - w) = ρ x w - w at he'
  rw [map_sub] at he'
  have hadd (v : W) : v + v = 0 := by
    have h := @two_smul (ZMod 2) W _ _ _ v
    simpa only [show (2 : ZMod 2) = 0 from by decide, zero_smul] using h.symm
  have hw : ρ x (ρ x w) = w := by
    apply add_right_cancel (b := w)
    exact (sub_eq_sub_iff_add_eq_add.mp he').trans ((hadd _).trans (hadd w).symm)
  change ρ ((x : H) ^ (2 ^ 1)) w = ρ (1 : H) w
  simpa only [pow_one, pow_two, map_mul, Module.End.mul_apply,
    map_one, Module.End.one_apply] using hw

theorem two_layer_restriction_faithful (ρ : Representation (ZMod 2) H W)
    (J : Subrepresentation ρ) (hf : Function.Injective ρ)
    (hd : ∀ g w, ρ g w - w ∈ J) (hc : pCore 2 H = ⊥) :
    Function.Injective J.toRepresentation := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact le_bot_iff.mp ((show J.toRepresentation.ker ≤ pCore 2 H from
    le_sSup ⟨inferInstance,two_layer_kernel_isTwoGroup ρ J hf hd⟩).trans_eq hc)

/-- Normal subgroups inherit the zero-core criterion for faithful two-layer restriction. -/
theorem normal_two_layer_restriction_faithful (ρ : Representation (ZMod 2) H W)
    (J : Subrepresentation ρ) (L : Subgroup H) [L.Normal]
    (hf : Function.Injective ρ)
    (hd : ∀ (g : L) w, ρ g w - w ∈ J) (hc : pCore 2 H = ⊥) :
    Function.Injective (J.toRepresentation.comp L.subtype) := by
  have hm : (pCore 2 L).map L.subtype ≤ pCore 2 H :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map L.subtype⟩
  have hb : pCore 2 L = ⊥ := ((pCore 2 L).map_eq_bot_iff_of_injective L.subtype_injective).mp
    (le_bot_iff.mp (hm.trans_eq hc))
  let J' : Subrepresentation (ρ.comp L.subtype) := {
    toSubmodule := J.toSubmodule
    apply_mem_toSubmodule := fun g => J.apply_mem_toSubmodule g }
  exact two_layer_restriction_faithful (ρ.comp L.subtype) J'
    (hf.comp L.subtype_injective) hd hb

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]
theorem dual_faithful_of_faithful (ρ : Representation k H M)
    (hf : Function.Injective ρ) : Function.Injective ρ.dual := by
  intro g h he
  apply inv_injective
  apply hf
  ext w
  apply Module.eval_apply_injective k
  ext f
  exact congrArg (fun e : Module.End k (Module.Dual k M) => e f w) he

theorem asGroupHom_injective_iff (ρ : Representation k H M) :
    Function.Injective ρ.asGroupHom ↔ Function.Injective ρ := by
  constructor
  · intro hf a b he
    apply hf
    exact Units.ext he
  · intro hf a b he
    apply hf
    exact congrArg Units.val he
end Representation

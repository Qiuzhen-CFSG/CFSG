module
public import Theory.Representation.ProjectiveIsotypicComplement
public import Theory.Representation.IsotypicCopies
public import Theory.Representation.NormalPairHomogeneous

/-!
# Canonical complements under automorphism twists

The intersection of kernels of all maps to a fixed simple representation is
preserved by an operator intertwining a compatible automorphism twist.
Together with the projective-injective splitting theorem, this produces an
invariant complement to the full isotypic component. The ambient module need
not be semisimple. This is used for the whole exceptional A₅ layer in
Aschbacher--Smith 5.1.14 and 5.1.19, printed pp.638,643--644.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped MonoidAlgebra
open Representation Module
namespace Representation
universe u v w z
variable {k : Type u} {D : Type v} {V : Type w} {E : Type z} [Field k] [Group D]
  [AddCommGroup V] [Module k V] [AddCommGroup E] [Module k E]

/-- The canonical part having no maps to the specified simple type. -/
def typeReject (ρ : Representation k D V) (σ : Representation k D E) : Subrepresentation ρ :=
  Subrepresentation.ofSubmodule' (Module.typeReject k[D] ρ.asModule σ.asModule)

theorem mem_typeReject_iff (ρ : Representation k D V) (σ : Representation k D E) (v : V) :
    v ∈ typeReject ρ σ ↔ ∀ f : ρ.IntertwiningMap σ, f v = 0 := by
  change (ρ.asModuleEquiv.symm v ∈ Module.typeReject k[D] ρ.asModule σ.asModule) ↔ _
  rw [Module.mem_typeReject]
  constructor
  · intro h f
    have hh := h (IntertwiningMap.equivLinearMapAsModule ρ σ f)
    exact congrArg σ.asModuleEquiv hh
  · intro h F
    have hh := h ((IntertwiningMap.equivLinearMapAsModule ρ σ).symm F)
    exact congrArg σ.asModuleEquiv.symm hh

/-- The kernel intersection is preserved by a compatible automorphism twist. -/
theorem typeReject_stable_of_covariance
    (ρ : Representation k D V) (σ : Representation k D E)
    (T : V →ₗ[k] V) (a : MulAut D) (c : E ≃ₗ[k] E)
    (hT : ∀ d v, T (ρ d v) = ρ (a d) (T v))
    (hc : ∀ d v, c (σ d v) = σ (a d) (c v))
    (v : V) (hv : v ∈ typeReject ρ σ) : T v ∈ typeReject ρ σ := by
  rw [mem_typeReject_iff] at hv ⊢
  intro f
  let f' : ρ.IntertwiningMap σ := {
    toLinearMap := c.symm.toLinearMap.comp (f.toLinearMap.comp T)
    isIntertwining' d := by
      apply LinearMap.ext
      intro w
      change c.symm (f (T (ρ d w))) = σ d (c.symm (f (T w)))
      rw [hT, f.isIntertwining]
      apply c.injective
      rw [c.apply_symm_apply, hc, c.apply_symm_apply] }
  have h := congrArg c (hv f')
  change c (c.symm (f (T v))) = c 0 at h
  simpa only [c.apply_symm_apply, map_zero] using h

/-- The actual type span and its canonical rejection complement one another. -/
theorem isCompl_typeSpan_typeReject [FiniteDimensional k V]
    (ρ : Representation k D V) (σ : Representation k D E) [σ.IsIrreducible]
    [Small.{z} k[D]] [Module.Injective k[D] σ.asModule]
    [Module.Projective k[D] σ.asModule] :
    IsCompl (typeSpan ρ σ) (typeReject ρ σ) := by
  let : Module.Finite k ρ.asModule := ρ.asModuleEquiv.symm.finiteDimensional
  let : Module.Finite k (isotypicComponent k[D] ρ.asModule σ.asModule) :=
    FiniteDimensional.of_injective
      ((isotypicComponent k[D] ρ.asModule σ.asModule).subtype.restrictScalars k)
      Subtype.val_injective
  let : Module.Finite k[D] (isotypicComponent k[D] ρ.asModule σ.asModule) :=
    Module.Finite.of_restrictScalars_finite k k[D] _
  rw [NormalPairHomogeneous.typeSpan_eq_isotypic]
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm.isCompl_iff.mp
    (Module.isCompl_isotypic_typeReject (R := k[D]) (M := ρ.asModule) (E := σ.asModule))
end Representation


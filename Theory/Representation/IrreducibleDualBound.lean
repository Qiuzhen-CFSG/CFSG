module
public import Theory.Representation.SubspaceQuotient
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A simple generator in a small natural--dual sum

If a simple module has no nonzero map to its dual, its images in X and X*
annihilate one another. When dim X is less than twice the simple dimension,
at most one image can be nonzero. Thus that simple module cannot generate
X plus X* under an overgroup preserving both summands.

Source application: Aschbacher--Smith 10.2.9, printed p.752, where an
original natural three-space generates the containing orbit module.
-/

public noncomputable section
open Representation
namespace Representation.IntertwiningMap
variable {k H W X : Type*} [Field k] [Group H]
  [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X] [FiniteDimensional k X]
  {ρ : Representation k H W} {σ : Representation k H X} [IsIrreducible ρ]

/-- A large simple module cannot embed in both a module and its dual. -/
theorem small_dual_pair
    (hzero : ∀ b : ρ.IntertwiningMap ρ.dual, b = 0)
    (hd : Module.finrank k X < 2 * Module.finrank k W)
    (f : ρ.IntertwiningMap σ) (g : ρ.IntertwiningMap σ.dual) :
    f = 0 ∨ g = 0 := by
  by_cases hf : f = 0
  · exact Or.inl hf
  by_cases hg : g = 0
  · exact Or.inr hg
  have hfi := (IsIrreducible.injective_or_eq_zero f).resolve_right hf
  have hgi := (IsIrreducible.injective_or_eq_zero g).resolve_right hg
  let b : ρ.IntertwiningMap ρ.dual := {
    toLinearMap := f.toLinearMap.dualMap.comp g.toLinearMap
    isIntertwining' := by
      intro h
      ext u v
      change g (ρ h u) (f v) = g u (f (ρ h⁻¹ v))
      rw [g.isIntertwining, f.isIntertwining]
      rfl }
  have hz (u v : W) : g u (f v) = 0 := by
    exact congrArg (fun c : ρ.IntertwiningMap ρ.dual => c u v) (hzero b)
  have hr : LinearMap.range g.toLinearMap ≤ (LinearMap.range f.toLinearMap).dualAnnihilator := by
    rintro _ ⟨u,rfl⟩
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro _ hv
    obtain ⟨v,rfl⟩ := hv
    exact hz u v
  have hfd : Module.finrank k (LinearMap.range f.toLinearMap) = Module.finrank k W :=
    (LinearEquiv.ofInjective f.toLinearMap hfi).finrank_eq.symm
  have hgd : Module.finrank k (LinearMap.range g.toLinearMap) = Module.finrank k W :=
    (LinearEquiv.ofInjective g.toLinearMap hgi).finrank_eq.symm
  have hle := Submodule.finrank_mono hr
  have he := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range f.toLinearMap)
  omega
end Representation.IntertwiningMap

namespace Representation
variable {k H A W X : Type*} [Field k] [Group H] [Group A]
  [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X] [FiniteDimensional k X] [Nontrivial X]
  {ρ : Representation k H W} [IsIrreducible ρ]
  (σ : Representation k A X) (q : H →* A)
  (f : ρ.IntertwiningMap ((σ.prod σ.dual).comp q))

/-- Orbit generation rules out a small natural--dual target. -/
theorem no_small_simple_dual_generator
    (hzero : ∀ b : ρ.IntertwiningMap ρ.dual, b = 0)
    (hd : Module.finrank k X < 2 * Module.finrank k W)
    (hgen : ∀ P : Subrepresentation (σ.prod σ.dual),
      (∀ w, f w ∈ P.toSubmodule) → P = ⊤) : False := by
  let a : ρ.IntertwiningMap (σ.comp q) := {
    toLinearMap := (LinearMap.fst _ _ _).comp f.toLinearMap
    isIntertwining' := by
      intro h
      ext w
      exact congrArg Prod.fst (LinearMap.congr_fun (f.isIntertwining' h) w) }
  let b : ρ.IntertwiningMap (Representation.dual (σ.comp q)) := {
    toLinearMap := (LinearMap.snd _ _ _).comp f.toLinearMap
    isIntertwining' := by
      intro h
      ext w x
      have he := congrArg (fun v => v.2 x) (LinearMap.congr_fun (f.isIntertwining' h) w)
      change (f (ρ h w)).2 x = (f w).2 (σ ((q h)⁻¹) x) at he
      change (f (ρ h w)).2 x = (f w).2 (σ (q h⁻¹) x)
      simpa only [map_inv] using he }
  obtain ⟨x,hx⟩ := exists_ne (0 : X)
  obtain ⟨y,hy⟩ := exists_ne (0 : Module.Dual k X)
  rcases IntertwiningMap.small_dual_pair hzero hd a b with ha | hb
  · let P : Subrepresentation (σ.prod σ.dual) := {
      toSubmodule := (LinearMap.fst k X (Module.Dual k X)).ker
      apply_mem_toSubmodule := by
        intro g v hv
        change v.1 = 0 at hv
        change σ g v.1 = 0
        rw [hv,map_zero] }
    have hP := hgen P (fun w => congrArg (fun z : ρ.IntertwiningMap (σ.comp q) => z w) ha)
    have hm : (x,0) ∈ P.toSubmodule := hP ▸ Submodule.mem_top
    exact hx hm
  · let P : Subrepresentation (σ.prod σ.dual) := {
      toSubmodule := (LinearMap.snd k X (Module.Dual k X)).ker
      apply_mem_toSubmodule := by
        intro g v hv
        change v.2 = 0 at hv
        change σ.dual g v.2 = 0
        rw [hv,map_zero] }
    have hP := hgen P (fun w => congrArg (fun z : ρ.IntertwiningMap (Representation.dual (σ.comp q)) => z w) hb)
    have hm : (0,y) ∈ P.toSubmodule := hP ▸ Submodule.mem_top
    exact hy hm
end Representation

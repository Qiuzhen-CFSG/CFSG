module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Algebra.Module.Projective
import Mathlib.RepresentationTheory.Maschke

/-!
# A trace criterion for projectivity

If the sum of conjugates of a linear endomorphism is the identity, average
its composite with a linear section of the free cover. The resulting section
is equivariant, so the group-algebra module is projective. On an irreducible
module the trace is an equivariant endomorphism, and fixing one nonzero vector
forces it to be the identity.

This is the trace criterion used below to prove the concrete projectivity
assertion of Aschbacher–Smith H.6.3(1), printed p.387, combined manuscript
of 1 March 2004. No assumption on invertibility of the group order is used.
-/

open scoped MonoidAlgebra
open Representation

public section

namespace Representation.ProjectiveTrace

/-- A linear endomorphism whose group trace is the identity splits the free cover. -/
theorem projective_of_norm {k G V : Type*} [Field k] [Group G] [Fintype G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (θ : Module.End k V)
    (hθ : ∀ v, ∑ g : G, ρ g⁻¹ (θ (ρ g v)) = v) :
    Module.Projective k[G] ρ.asModule := by
  let f : (ρ.asModule →₀ k[G]) →ₗ[k[G]] ρ.asModule :=
    Finsupp.linearCombination k[G] id
  have hf : Function.Surjective f :=
    Finsupp.linearCombination_surjective _ Function.surjective_id
  obtain ⟨s, hs⟩ := (f.restrictScalars k).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hf)
  let θ' : Module.End k ρ.asModule := ρ.asModuleEquiv.symm.toLinearMap ∘ₗ θ ∘ₗ
    ρ.asModuleEquiv.toLinearMap
  refine ⟨⟨(s ∘ₗ θ').sumOfConjugatesEquivariant G, ?_⟩⟩
  intro v
  change f ((s ∘ₗ θ').sumOfConjugatesEquivariant G v) = v
  rw [LinearMap.sumOfConjugatesEquivariant_apply, map_sum]
  simp only [LinearMap.conjugate_apply, f.map_smul]
  have hs' (w : ρ.asModule) : f (s w) = w := LinearMap.congr_fun hs w
  simp only [LinearMap.comp_apply, hs']
  apply ρ.asModuleEquiv.injective
  rw [map_sum]
  simp only [θ', LinearMap.comp_apply, LinearEquiv.coe_coe, asModuleEquiv_map_smul,
    asAlgebraHom_single, one_smul, LinearEquiv.apply_symm_apply]
  exact hθ _

/-- On an irreducible representation, it suffices that the group trace fixes one nonzero vector. -/
theorem projective_of_norm_fixed {k G V : Type*} [Field k] [Group G] [Fintype G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) [IsIrreducible ρ]
    (θ : Module.End k V) (v : V) (hv : v ≠ 0)
    (hθ : ∑ g : G, ρ g⁻¹ (θ (ρ g v)) = v) :
    Module.Projective k[G] ρ.asModule := by
  let θ' : Module.End k ρ.asModule := ρ.asModuleEquiv.symm.toLinearMap ∘ₗ θ ∘ₗ
    ρ.asModuleEquiv.toLinearMap
  let F : Module.End k[G] ρ.asModule := θ'.sumOfConjugatesEquivariant G
  have hF (w : V) : ρ.asModuleEquiv (F (ρ.asModuleEquiv.symm w)) =
      ∑ g : G, ρ g⁻¹ (θ (ρ g w)) := by
    rw [LinearMap.sumOfConjugatesEquivariant_apply, map_sum]
    simp only [LinearMap.conjugate_apply, θ', LinearMap.comp_apply,
      LinearEquiv.coe_coe, asModuleEquiv_map_smul, asAlgebraHom_single,
      one_smul, LinearEquiv.apply_symm_apply]
  have hfix : F (ρ.asModuleEquiv.symm v) = ρ.asModuleEquiv.symm v := by
    apply ρ.asModuleEquiv.injective
    rw [hF, hθ, LinearEquiv.apply_symm_apply]
  have hzero : F - LinearMap.id = 0 :=
    (LinearMap.injective_or_eq_zero (F - LinearMap.id)).resolve_left (by
      intro hi
      have he : ρ.asModuleEquiv.symm v = 0 := hi (by
        simp only [LinearMap.sub_apply, LinearMap.id_apply, hfix, sub_self, map_zero])
      apply hv
      simpa using congrArg ρ.asModuleEquiv he)
  apply projective_of_norm ρ θ
  intro w
  rw [← hF, sub_eq_zero.mp hzero]
  exact ρ.asModuleEquiv.apply_symm_apply w

end Representation.ProjectiveTrace

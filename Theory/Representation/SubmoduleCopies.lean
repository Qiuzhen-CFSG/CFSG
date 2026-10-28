module
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.Length
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Pi

/-!
# Restricting a finite sum of copies of a simple module

An embedded submodule of m copies of a simple module is semisimple and
isotypic. A nonzero coordinate projection identifies each simple summand;
module length bounds its multiplicity by m. The representation version
retains the original actor and explicitly intertwines the new coordinates.

Source application: Aschbacher–Smith, 12.2.7(3i) and 12.3.2, printed
pp.797,807, restricting the whole reduced layer to the moved omega-span.
-/

public noncomputable section
open scoped MonoidAlgebra
namespace Module
variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [IsSimpleModule R M] [AddCommGroup N] [Module R N]

/-- Restriction cannot increase the multiplicity of a simple type. -/
theorem copies_of_injective {m : ℕ} (f : N →ₗ[R] (Fin m → M))
    (hf : Function.Injective f) :
    ∃ n : ℕ, n ≤ m ∧ Nonempty (N ≃ₗ[R] (Fin n → M)) := by
  let : IsSemisimpleModule R N := IsSemisimpleModule.of_injective f hf
  let : Module.Finite R N := Module.Finite.of_injective f hf
  have ht : IsIsotypicOfType R N M := by
    intro S hS
    let := hS
    let := IsSimpleModule.nontrivial R S
    obtain ⟨v,hv⟩ := exists_ne (0 : S)
    have hfv : f v.val ≠ 0 := by
      intro he
      exact hv (Subtype.ext (hf (he.trans f.map_zero.symm)))
    obtain ⟨i,hi⟩ : ∃ i, f v.val i ≠ 0 := by
      by_contra he
      exact hfv (funext fun i => not_ne_iff.mp (not_exists.mp he i))
    let p : S →ₗ[R] M := (LinearMap.proj i).comp (f.comp S.subtype)
    have hp : p ≠ 0 := fun he => hi (DFunLike.congr_fun he v)
    exact ⟨LinearEquiv.ofBijective p (LinearMap.bijective_of_ne_zero hp)⟩
  obtain ⟨n,⟨e⟩⟩ := ht.linearEquiv_fun
  refine ⟨n,?_,⟨e⟩⟩
  have hlen := Module.length_le_of_injective f hf
  rw [e.length_eq] at hlen
  simpa using hlen
end Module

namespace Representation
variable {k A V E : Type*} [Field k] [Group A]
  [AddCommGroup V] [Module k V] [AddCommGroup E] [Module k E]
  (τ : Representation k A V) (σ : Representation k A E) [IsIrreducible σ]

set_option backward.isDefEq.respectTransparency false in
/-- The finite-copy coordinates preserve the specified group action. -/
theorem coordinates_of_embedding_copies {m : ℕ} (f : V →ₗ[k] (Fin m → E))
    (hf : Function.Injective f)
    (ha : ∀ a v i, f (τ a v) i = σ a (f v i)) :
    ∃ n : ℕ, n ≤ m ∧ ∃ e : V ≃ₗ[k] (Fin n → E),
      ∀ a v i, e (τ a v) i = σ a (e v i) := by
  let p (i : Fin m) : τ.IntertwiningMap σ := {
    toLinearMap := (LinearMap.proj i).comp f
    isIntertwining' a := LinearMap.ext (fun v => ha a v i) }
  let F : τ.asModule →ₗ[k[A]] (Fin m → σ.asModule) :=
    LinearMap.pi (fun i => IntertwiningMap.equivLinearMapAsModule τ σ (p i))
  have hF : Function.Injective F := hf
  obtain ⟨n,hn,⟨b⟩⟩ := Module.copies_of_injective F hF
  let e : V ≃ₗ[k] (Fin n → E) := τ.asModuleEquiv.symm.trans
    ((b.restrictScalars k).trans (LinearEquiv.piCongrRight fun _ => σ.asModuleEquiv))
  refine ⟨n,hn,e,?_⟩
  intro a v i
  change σ.asModuleEquiv (b (τ.asModuleEquiv.symm (τ a v)) i) = _
  rw [τ.asModuleEquiv_symm_map_rho, b.map_smul]
  change σ.asModuleEquiv ((MonoidAlgebra.of k A a) • b (τ.asModuleEquiv.symm v) i) = _
  rw [Representation.asModuleEquiv_map_smul]
  rw [Representation.asAlgebraHom_of]
  rfl
end Representation

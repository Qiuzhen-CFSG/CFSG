module

public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Quadratic actions on equivariant quotients

A surjective intertwining linear map preserves quadratic action. It induces
a surjection on quotients by fixed spaces, so fixed codimension cannot increase.
Thus a module with quadratic action ratio at most two cannot have a quotient
whose quadratic action ratio is strictly greater than two.

This is the quotient step used to remove the Steinberg summands in
Aschbacher–Smith 13.8.19, printed p.953 (1 March 2004 manuscript).
-/

public section
namespace Representation.BinaryOffender
open Representation.BinaryOffender
variable {H U V : Type*} [Group H]
  [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) H U) (σ : Representation (ZMod 2) H V)

theorem quadratic_of_equivariant_surjection (f : U →ₗ[ZMod 2] V) (hf : Function.Surjective f)
    (he : ∀ g v, f (ρ g v) = σ g (f v)) (A : Subgroup H)
    (hq : IsQuadratic ρ A) : IsQuadratic σ A := by
  intro a ha b hb v
  obtain ⟨u, rfl⟩ := hf v
  have hh := congrArg f (hq a ha b hb u)
  simpa only [he, map_sub] using hh

theorem fixedCodim_le_of_equivariant_surjection [FiniteDimensional (ZMod 2) U]
    (f : U →ₗ[ZMod 2] V) (hf : Function.Surjective f)
    (he : ∀ g v, f (ρ g v) = σ g (f v)) (A : Subgroup H) :
    fixedCodim σ A ≤ fixedCodim ρ A := by
  have hfix : fixedSpace ρ A ≤ (fixedSpace σ A).comap f := by
    intro u hu a
    change σ a (f u) = f u
    rw [← he]
    exact congrArg f (hu a)
  let q := (fixedSpace ρ A).mapQ (fixedSpace σ A) f hfix
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨w, rfl⟩ := (fixedSpace σ A).mkQ_surjective v
    obtain ⟨u, rfl⟩ := hf w
    exact ⟨(fixedSpace ρ A).mkQ u, rfl⟩
  exact LinearMap.finrank_le_finrank_of_surjective hq

variable [FiniteDimensional (ZMod 2) U]
theorem not_small_quadratic_of_equivariant_quotient
    (f : U →ₗ[ZMod 2] V) (hf : Function.Surjective f)
    (he : ∀ g v, f (ρ g v) = σ g (f v))
    (hσ : ∀ A, IsElementaryTwo A → IsQuadratic σ A →
      2 * rank A < fixedCodim σ A)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) : False := by
  have hqσ := quadratic_of_equivariant_surjection ρ σ f hf he A hq
  have hlt := hσ A hA hqσ
  have hle := fixedCodim_le_of_equivariant_surjection ρ σ f hf he A
  omega
end Representation.BinaryOffender


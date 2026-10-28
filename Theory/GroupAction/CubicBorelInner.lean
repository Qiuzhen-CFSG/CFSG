module

public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Cubic innerness detected on a Sylow normalizer

This intrinsic property detects inner cubic automorphisms from their action
on a Sylow two-normalizer modulo its Sylow subgroup. Each displacement is
allowed to have three-power order. In particular the normalizer itself may
have order divisible by three.

The transport theorem uses the actual group equivalence, including the
Sylow subgroup, its normalizer, and the inner automorphism subgroup.
Concrete model proofs must establish the property separately.

Source: the Borel-action step of Aschbacher--Smith, proof of 15.3.37,
`refs/quasithin.pdf`, printed p.1135.
-/

@[expose] public section

namespace MulAut
open Subgroup

/-- A cubic actor with three-primary displacements on the Sylow normalizer
quotient is inner. This is a model property, not an automorphism hypothesis
of the source theorem. -/
def CubicBorelInner (D : Type*) [Group D] : Prop :=
  ∀ P : Sylow 2 D, ∀ α : MulAut D, α ^ 3 = 1 →
    (∀ x ∈ P, α x ∈ P) →
    (∀ b ∈ normalizer (P : Set D), ∃ k : ℕ,
      (α b * b⁻¹) ^ (3 ^ k) ∈ P) → α ∈ innerSubgroup D

/-- The detector transports through a genuine group isomorphism. -/
theorem CubicBorelInner.of_mulEquiv {D E : Type*} [Group D] [Group E]
    [Finite D] (hE : CubicBorelInner E) (e : D ≃* E) : CubicBorelInner D := by
  intro P α hα hP hB
  let Q : Sylow 2 E := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : (Q : Subgroup E) = (P : Subgroup D).map e.toMonoidHom := rfl
  have hnorm : (normalizer (P : Set D)).map e.toMonoidHom =
      normalizer (Q : Set E) := map_equiv_normalizer_eq _ e
  have hβ : MulAut.congr e α ∈ innerSubgroup E := hE Q (MulAut.congr e α)
    (by rw [← map_pow, hα, map_one]) (by
      intro x hx
      change x ∈ (Q : Subgroup E) at hx
      rw [hQ] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      change e (α (e.symm (e y))) ∈ (Q : Subgroup E)
      rw [e.symm_apply_apply, hQ]
      exact mem_map_of_mem _ (hP y hy)) (by
      intro x hx
      rw [← hnorm] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨k, hk⟩ := hB y hy
      refine ⟨k, ?_⟩
      change (e (α (e.symm (e y))) * (e y)⁻¹) ^ (3 ^ k) ∈ (Q : Subgroup E)
      rw [e.symm_apply_apply, ← map_inv, ← map_mul, ← map_pow, hQ]
      exact mem_map_of_mem _ hk)
  rw [← map_innerSubgroup_congr e] at hβ
  obtain ⟨β, hβ, he⟩ := hβ
  exact (MulAut.congr e).injective he ▸ hβ

end MulAut

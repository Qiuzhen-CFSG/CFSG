module

public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Cubic rigidity on a Sylow normalizer quotient

This interface isolates an intrinsic automorphism calculation. A cubic
actor preserving a Sylow two-subgroup and inducing the identity on its
normalizer quotient must be trivial when that normalizer has order prime
to three. It is a property to be proved for a concrete group, not an
assumed automorphism classification or a statement of a source theorem.

The intended application is the torus/field step in Aschbacher–Smith,
`refs/quasithin.pdf`, printed p.1144, proof of 15.3.49(k).
-/

@[expose] public section

namespace MulAut

/-- The precise intrinsic cubic-automorphism calculation needed by Borel control.
The displacement condition expresses trivial action on the actual normalizer
modulo its Sylow subgroup. -/
def CubicBorelRigid (D : Type*) [Group D] : Prop :=
  ∀ P : Sylow 2 D, ¬ 3 ∣ Nat.card (Subgroup.normalizer (P : Set D)) →
    ∀ α : MulAut D, α ^ 3 = 1 →
      (∀ x ∈ P, α x ∈ P) →
      (∀ b ∈ Subgroup.normalizer (P : Set D), α b * b⁻¹ ∈ P) → α = 1

open Subgroup

/-- Cubic Borel rigidity is invariant under actual group isomorphisms. -/
theorem CubicBorelRigid.of_mulEquiv {D E : Type*} [Group D] [Group E]
    [Finite D] (hE : CubicBorelRigid E) (e : D ≃* E) : CubicBorelRigid D := by
  intro P hN α hα hP hB
  let Q : Sylow 2 E := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : (Q : Subgroup E) = (P : Subgroup D).map e.toMonoidHom := rfl
  have hnorm : (normalizer (P : Set D)).map e.toMonoidHom = normalizer (Q : Set E) := by
    change (normalizer ((P : Subgroup D) : Set D)).map (e : D →* E) =
      normalizer ((P : Subgroup D).map (e : D →* E) : Set E)
    exact map_equiv_normalizer_eq _ e
  have hthree : ¬ 3 ∣ Nat.card (normalizer (Q : Set E)) := by
    have hc := Nat.card_congr (e.subgroupMap (normalizer (P : Set D))).toEquiv
    change Nat.card (normalizer (P : Set D)) =
      Nat.card ((normalizer (P : Set D)).map e.toMonoidHom) at hc
    rw [hnorm] at hc
    rwa [← hc]
  have hβ := hE Q hthree (MulAut.congr e α)
    (by rw [← map_pow, hα, map_one])
  have heq : MulAut.congr e α = 1 := hβ (by
    intro x hx
    change x ∈ (Q : Subgroup E) at hx
    rw [hQ] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    change e (α (e.symm (e y))) ∈ (Q : Subgroup E)
    rw [e.symm_apply_apply, hQ]
    exact mem_map_of_mem _ (hP y hy)) (by
    intro x hx
    rw [← hnorm] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    change e (α (e.symm (e y))) * (e y)⁻¹ ∈ (Q : Subgroup E)
    rw [e.symm_apply_apply, ← map_inv, ← map_mul, hQ]
    exact mem_map_of_mem _ (hB y hy))
  exact (MulAut.congr e).injective (heq.trans (map_one _).symm)

end MulAut

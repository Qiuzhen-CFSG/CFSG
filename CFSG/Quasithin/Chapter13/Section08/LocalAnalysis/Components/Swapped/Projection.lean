module

public import Mathlib.RepresentationTheory.Coinvariants

/-!
# The diagonal projection contradiction in 13.8.16

If the second direct factor acts trivially, two elements with the same first
coordinate induce the same endomorphism. Apply this to two actual diagonal
homomorphisms: one fixes the seed projection, while the other generates the
seed by commutators. Equivariance then forces the projection to vanish.
A nonzero subspace invariant under an action exchanging the factors,
however, has a nonzero first projection. The exchanging element need not
be an involution: its two coordinate maps need not be mutual inverses.

These are linear deductions from compatible actions, not assumed diagonal
action identities. The source application still has to construct the two
diagonal embeddings, the equivariant module projections and the swapping
action from its earlier group and representation classifications.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.16, cases (a) and (b1), printed p.952 (PDF p.969).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped
variable {k A P Q V W : Type*} [CommRing k] [Group A] [Group P] [Group Q]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Product coordinates determine the action when the second factor is trivial. -/
theorem action_eq_of_trivial_second_factor (ρ : Representation k (P × Q) W)
    (hQ : ∀ q : Q, ρ (1, q) = 1) (p : P) (q₀ q₁ : Q) :
    ρ (p, q₀) = ρ (p, q₁) := by
  have he (q : Q) : ρ (p, q) = ρ (p, 1) := by
    calc
      ρ (p, q) = ρ ((p, 1) * (1, q)) := by simp
      _ = ρ (p, 1) := by rw [map_mul, hQ, mul_one]
  exact (he q₀).trans (he q₁).symm

/-- An equivariant projection vanishes when one diagonal fixes its image and the other generates its domain by commutators. -/
theorem projection_eq_zero_of_diagonal_actions
    (σ : Representation k A V) (ρ : Representation k (P × Q) W)
    (i : A →* P) (d₀ d₁ : A →* Q) (f : V →ₗ[k] W)
    (hQ : ∀ q : Q, ρ (1, q) = 1)
    (hequiv : ∀ a x, f (σ a x) = ρ (i a, d₁ a) (f x))
    (hfixed : ∀ a x, ρ (i a, d₀ a) (f x) = f x)
    (hgen : Representation.Coinvariants.ker σ = ⊤) : f = 0 := by
  have hfix (a : A) (x : V) : f (σ a x) = f x := by
    rw [hequiv, action_eq_of_trivial_second_factor ρ hQ (i a) (d₁ a) (d₀ a)]
    exact hfixed a x
  have hker : Representation.Coinvariants.ker σ ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, x⟩, rfl⟩
    change f (σ a x - x) = 0
    rw [map_sub, hfix, sub_self]
  rw [hgen, top_le_iff] at hker
  exact LinearMap.ker_eq_top.mp hker

/-- A nonzero subspace stable under an identified factor exchange has nonzero projection.
The two exchange maps need not be mutual inverses. -/
theorem nonzero_first_projection_of_swap_invariant
    (e₁₂ : V ≃ₗ[k] W) (e₂₁ : W ≃ₗ[k] V)
    (X : Submodule k (V × W)) (hne : X ≠ ⊥)
    (hswap : ∀ x ∈ X, (e₂₁ x.2, e₁₂ x.1) ∈ X) :
    ∃ x ∈ X, x.1 ≠ 0 := by
  by_contra hn
  push Not at hn
  apply hne
  apply le_antisymm _ bot_le
  intro x hx
  have hx₁ := hn x hx
  have hx₂ : x.2 = 0 := by
    have h := hn (e₂₁ x.2, e₁₂ x.1) (hswap x hx)
    simpa only [LinearEquiv.map_eq_zero_iff] using h
  exact Prod.ext hx₁ hx₂

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped

end

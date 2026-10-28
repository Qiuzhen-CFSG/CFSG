module

public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_2_f

/-!
This module isolates `theorem_2_1_2_g` from `Theory.AlgebraicGroup.Automorphisms.Lang`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

universe u v

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_2_1_2_g
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (hK : IsSemisimpleAlgebraicGroup K) :
    ∀ m : ℕ, 0 < m →
      Function.Surjective (σ.onPoints^[m]) ∧
        Finite {x : Variety.Point K | σ.onPoints^[m] x = x} := by
  sorry

public theorem theorem_2_1_2_converse
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K) (m : ℕ) (hm : 0 < m)
    (hσm : Function.Surjective (σ.onPoints^[m]) ∧
      Finite {x : Variety.Point K | σ.onPoints^[m] x = x}) :
    IsAlgebraicSteinbergEndomorphism σ := by
  have hsurj : Function.Surjective σ.onPoints := by
    intro y
    obtain ⟨x, hx⟩ := hσm.1 y
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    refine ⟨(σ.onPoints^[n]) x, ?_⟩
    rw [hn, Function.iterate_succ_apply'] at hx
    exact hx
  let : Finite {x : Variety.Point K | σ.onPoints^[m] x = x} := hσm.2
  have hfixedFinite :
      ({x : Variety.Point K | σ.onPoints x = x} : Set (Variety.Point K)).Finite := by
    apply (Set.toFinite
      ({x : Variety.Point K | σ.onPoints^[m] x = x} : Set (Variety.Point K))).subset
    intro x hx
    exact Function.iterate_fixed hx m
  exact ⟨hsurj, Set.finite_coe_iff.mpr hfixedFinite⟩

end Theory.AlgebraicGroup

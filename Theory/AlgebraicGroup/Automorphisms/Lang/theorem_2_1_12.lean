module

public import Theory.AlgebraicGroup.Automorphisms.Lang.root_subgroup_fixed_count
public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_11

/-!
This module isolates `theorem_2_1_12` from `Theory.AlgebraicGroup.Automorphisms.Lang`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

universe u v

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_2_1_12
    {K : Variety k} [AlgebraicGroup K]
    {r : ℕ} [Fact r.Prime] [CharP k r]
    (σ : AlgebraicGroup.Morphism K K)
    (hK : IsSemisimpleAlgebraicGroup K)
    (hKne : Nontrivial (Variety.Point K))
    (q₀ : NNReal)
    (hσ : IsFrobeniusEndomorphismOfLevel (r := r) q₀ σ) :
    (∃ (T X : ClosedSubgroup K),
      IsMaximalTorus T ∧ IsTorusRootSubgroup T X ∧
      ∃ m : ℕ, 0 < m ∧
        Set.MapsTo (σ.onPoints^[m])
          (X : Set (Variety.Point K))
          (X : Set (Variety.Point K)) ∧
        Set.SurjOn (σ.onPoints^[m])
          (X : Set (Variety.Point K))
          (X : Set (Variety.Point K))) ∧
    ∀ (T X : ClosedSubgroup K),
      IsMaximalTorus T → IsTorusRootSubgroup T X →
      ∀ (m : ℕ), 0 < m →
        Set.MapsTo (σ.onPoints^[m])
          (X : Set (Variety.Point K))
          (X : Set (Variety.Point K)) →
        Set.SurjOn (σ.onPoints^[m])
          (X : Set (Variety.Point K))
          (X : Set (Variety.Point K)) →
        ((Set.ncard {x : Variety.Point K |
          x ∈ X.toSubgroup ∧ σ.onPoints^[m] x = x} : ℕ) : NNReal) = q₀ ^ m := by
  sorry

/-! The book's Notation 2.1.13 chooses a canonical level only after proving
uniqueness.  Until that uniqueness theorem is available, the honest interface
is the relation `IsFrobeniusEndomorphismOfLevel`; no witness-dependent choice is
exported here. -/

end Theory.AlgebraicGroup

module

public import Theory.AlgebraicGroup.Automorphisms.Lang.proposition_2_1_10

/-!
This module isolates `theorem_2_1_11` from `Theory.AlgebraicGroup.Automorphisms.Lang`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

universe u v

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_2_1_11
    {K : Variety k} [AlgebraicGroup K]
    {r : ℕ} [Fact r.Prime] [CharP k r]
    (σ : AlgebraicGroup.Morphism K K) :
    (IsFrobeniusEndomorphism (r := r) σ →
      IsAlgebraicSteinbergEndomorphism σ) ∧
    (IsSimpleAlgebraicGroup K →
      IsAlgebraicSteinbergEndomorphism σ →
      IsFrobeniusEndomorphism (r := r) σ) := by
  sorry

end Theory.AlgebraicGroup

module

public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The outer automorphism order of binary PSL₂

The proved semilinear coverage identifies the full outer group of PSL₂(F)
with the field automorphisms. A finite field of order 2ⁿ has exactly n
such automorphisms. In particular the actual outer group of PSL₂(8) has
order three, without an automorphism-classification premise.

Source: GLS3, Theorem 2.5.12, characteristic-two A₁; the finite-field
Frobenius theorem and the imported semilinear coverage proof.
-/

public section
namespace Theory.PSL2

/-- The actual binary outer quotient has order equal to the field degree. -/
theorem outer_card_eq_field_degree
    (F : Type*) [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : Nat.card (MulAut.Outer (Group F)) = n := by
  change Nat.card (MulAut (Group F) ⧸ inner F) = n
  rw [← Nat.card_congr (fieldOuterEquiv F).toEquiv]
  exact FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF

/-- The genuine PSL₂(8) outer group has order three. -/
theorem psl_eight_outer_card :
    Nat.card (MulAut.Outer (BinaryGroup 3)) = 3 :=
  outer_card_eq_field_degree (BinaryField 3) (GaloisField.card 2 3 (by decide))

end Theory.PSL2

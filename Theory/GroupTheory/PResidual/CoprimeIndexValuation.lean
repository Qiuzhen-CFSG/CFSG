module

public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Prime parts of residual orders

Taking the q-residual of a finite group preserves its p-part for distinct
primes p and q: the quotient has q-power order, and subgroup order times
index is the group order. This applies without a splitting hypothesis.

This is the elementary order calculation used for the modified residuals
in Aschbacher–Smith, Notation 16.5.5, printed p.1197.
-/

public section
namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- Passing to a residual at another prime preserves the p-part of the order. -/
theorem pResidual_card_padicValNat (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) :
    padicValNat p (Nat.card (pResidual q G)) = padicValNat p (Nat.card G) := by
  obtain ⟨n, hn⟩ := (isPGroup_quotient_pResidual (G := G) q).exists_card_eq
  have hi : (pResidual q G).index = q ^ n := by
    rw [index_eq_card, hn]
  rw [← (pResidual q G).card_mul_index, hi,
    padicValNat.mul (Nat.card_pos.ne') (pow_ne_zero _ (Fact.out : q.Prime).ne_zero),
    padicValNat_prime_prime_pow n hpq, add_zero]

end Subgroup

module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Parameters and cubic coefficient fields for triality

For every prime power `q = p^f`, with `f > 0`, the standard graph-field
construction uses `GF(p^(3*f))` and its `q`-power Frobenius. This module
constructs that coefficient field and automorphism in every characteristic.
The third iterate is the identity by the finite-field power identity.

These are the scalar data in GLS3, §§2.1–2.3
(`refs/KGroup/GLS3/chapter2.tex`). No group is identified as a triality group
here; the outer D4 diagram action must be constructed separately.
-/

@[expose] public section

namespace Triality.Standard

/-- The source parameter is an arbitrary positive power of a prime. -/
structure Parameters where
  prime : ℕ
  exponent : ℕ
  prime_prime : prime.Prime
  exponent_pos : 0 < exponent

instance (P : Parameters) : Fact P.prime.Prime := ⟨P.prime_prime⟩

/-- The order of the base field. -/
def Parameters.q (P : Parameters) : ℕ := P.prime ^ P.exponent

theorem Parameters.q_isPrimePow (P : Parameters) : IsPrimePow P.q := by
  exact (isPrimePow_nat_iff _).mpr
    ⟨P.prime, P.exponent, P.prime_prime, P.exponent_pos, rfl⟩

theorem Parameters.q_ge_two (P : Parameters) : 2 ≤ P.q := by
  exact Nat.succ_le_of_lt
    (one_lt_pow₀ P.prime_prime.one_lt (Nat.ne_of_gt P.exponent_pos))

/-- Every prime power has scalar data for the triality construction. -/
theorem exists_parameters (q : ℕ) (hq : IsPrimePow q) :
    ∃ P : Parameters, P.q = q := by
  obtain ⟨p, f, hp, hf, hq⟩ := (isPrimePow_nat_iff q).mp hq
  exact ⟨⟨p, f, hp, hf⟩, hq⟩

/-- The cubic extension of the field of order `P.q`. -/
abbrev ExtensionField (P : Parameters) := GaloisField P.prime (3 * P.exponent)

theorem card_extensionField (P : Parameters) :
    Nat.card (ExtensionField P) = P.q ^ 3 := by
  rw [GaloisField.card P.prime (3 * P.exponent) (by have := P.exponent_pos; omega)]
  simp only [Parameters.q, ← pow_mul, Nat.mul_comm 3 P.exponent]

/-- The field part of the graph-field automorphism. -/
noncomputable def fieldFrobenius (P : Parameters) :
    ExtensionField P ≃+* ExtensionField P :=
  iterateFrobeniusEquiv (ExtensionField P) P.prime P.exponent

@[simp] theorem fieldFrobenius_apply (P : Parameters) (x : ExtensionField P) :
    fieldFrobenius P x = x ^ P.q := rfl

/-- The cubic extension makes the third iterate of the field action trivial. -/
theorem fieldFrobenius_three (P : Parameters) (x : ExtensionField P) :
    fieldFrobenius P (fieldFrobenius P (fieldFrobenius P x)) = x := by
  classical
  let : Fintype (ExtensionField P) := Fintype.ofFinite _
  have hcard : Fintype.card (ExtensionField P) = P.q ^ 3 := by
    simpa only [Nat.card_eq_fintype_card] using card_extensionField P
  simpa only [fieldFrobenius_apply, ← pow_mul, pow_succ, pow_zero, one_mul, hcard]
    using (FiniteField.pow_card x)

theorem fieldFrobenius_pow_three (P : Parameters) :
    fieldFrobenius P ^ 3 = 1 := by
  ext x
  exact fieldFrobenius_three P x

end Triality.Standard

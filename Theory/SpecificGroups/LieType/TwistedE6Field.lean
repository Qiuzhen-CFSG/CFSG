module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.CharP.Frobenius

/-!
# The quadratic coefficient field for twisted E6

For `q = p^(m+1)`, the coefficient field has order `q²`. The twisting field
map is the `q`-power automorphism, whose square is the identity. Using `m+1`
includes every positive prime-power parameter, including `q = 2`.

These are coefficient data for the pinned graph-field construction of
GLS3, §§2.1–2.3 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

namespace TwistedE6

variable (p : ℕ) [Fact p.Prime]

/-- The field parameter; the exponent is positive. -/
def parameter (m : ℕ) : ℕ := p ^ (m + 1)

/-- The canonical splitting field with `q²` elements. -/
noncomputable abbrev CoefficientField (m : ℕ) : Type :=
  GaloisField p (2 * (m + 1))

noncomputable instance (m : ℕ) : Fintype (CoefficientField p m) :=
  Fintype.ofFinite _

theorem field_card (m : ℕ) :
    Nat.card (CoefficientField p m) = parameter p m ^ 2 := by
  rw [GaloisField.card p (2 * (m + 1)) (by omega), parameter, ← pow_mul]
  congr 1
  omega

theorem parameter_ge_two (m : ℕ) : 2 ≤ parameter p m := by
  have hp := (Fact.out : p.Prime).two_le
  exact le_trans hp (Nat.le_pow (by omega))

/-- The actual `q`-power field automorphism. -/
noncomputable def fieldTwist (m : ℕ) :
    CoefficientField p m ≃+* CoefficientField p m :=
  iterateFrobeniusEquiv (CoefficientField p m) p (m + 1)

@[simp] theorem fieldTwist_apply (m : ℕ) (x : CoefficientField p m) :
    fieldTwist p m x = x ^ parameter p m := rfl

@[simp] theorem fieldTwist_twice (m : ℕ) (x : CoefficientField p m) :
    fieldTwist p m (fieldTwist p m x) = x := by
  simp only [fieldTwist_apply, ← pow_mul, ← pow_two]
  rw [← field_card, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

end TwistedE6

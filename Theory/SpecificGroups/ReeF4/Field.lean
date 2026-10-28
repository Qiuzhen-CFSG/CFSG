module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.CharP.Frobenius

/-!
# The coefficient field for the large Ree groups

The parameter `m` denotes the group with field size `2^(2*m+1)`. The simple
family uses `1 ≤ m`; `m = 0` gives the field of order two, without identifying
the full nonsimple Ree group with its simple derived subgroup.

The field is Mathlib's splitting-field construction. Its Tits automorphism is
the `(m+1)`st power of Frobenius. Applying it twice gives squaring, since the
`(2*m+1)`st power of Frobenius is the identity. These are coefficient-field
ingredients for the exceptional twisted construction, not a definition of a
Ree group.

Source for the family and parameter convention: Aschbacher–Smith,
*The Classification of Quasithin Groups*, Theorem 0.1.2 and Remark A.2.4
(`refs/quasithin.pdf`).
-/

@[expose] public section

namespace ReeF4

/-- The canonical field of order `2^(2*m+1)`. -/
noncomputable abbrev CoefficientField (m : ℕ) : Type :=
  GaloisField 2 (2 * m + 1)

noncomputable instance (m : ℕ) : Fintype (CoefficientField m) :=
  Fintype.ofFinite _

theorem field_card (m : ℕ) :
    Nat.card (CoefficientField m) = 2 ^ (2 * m + 1) :=
  GaloisField.card 2 (2 * m + 1) (by omega)

theorem field_pow (m : ℕ) (x : CoefficientField m) :
    x ^ (2 ^ (2 * m + 1)) = x := by
  rw [← field_card m, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

/-- The field endomorphism `x ↦ x^(2^(m+1))`. -/
noncomputable def titsEnd (m : ℕ) : CoefficientField m →+* CoefficientField m :=
  iterateFrobenius (CoefficientField m) 2 (m + 1)

theorem titsEnd_apply (m : ℕ) (x : CoefficientField m) :
    titsEnd m x = x ^ (2 ^ (m + 1)) := rfl

theorem titsEnd_twice (m : ℕ) (x : CoefficientField m) :
    titsEnd m (titsEnd m x) = x ^ 2 := by
  change (x ^ (2 ^ (m + 1))) ^ (2 ^ (m + 1)) = x ^ 2
  rw [← pow_mul, ← pow_add]
  have he : m + 1 + (m + 1) = (2 * m + 1) + 1 := by omega
  rw [he, pow_succ, pow_mul, field_pow]

/-- The Tits field automorphism, with its inverse supplied by finite-field
bijectivity. -/
noncomputable def titsAutomorphism (m : ℕ) :
    CoefficientField m ≃+* CoefficientField m :=
  RingEquiv.ofBijective (titsEnd m)
    (Finite.injective_iff_bijective.mp (titsEnd m).injective)

theorem titsAutomorphism_apply (m : ℕ) (x : CoefficientField m) :
    titsAutomorphism m x = x ^ (2 ^ (m + 1)) := rfl

theorem titsAutomorphism_twice (m : ℕ) (x : CoefficientField m) :
    titsAutomorphism m (titsAutomorphism m x) = x ^ 2 :=
  titsEnd_twice m x

end ReeF4

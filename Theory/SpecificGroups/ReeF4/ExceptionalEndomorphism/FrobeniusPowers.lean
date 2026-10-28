module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.Frobenius

/-!
# Powers of Frobenius on the finite split F4 group

The `n`th compositional power of Frobenius raises every matrix entry to
`2^n`. The coefficient field has order `2^(2*m+1)`, so the `(2*m+1)`st
power is the identity. We package the existing homomorphism as a
`Monoid.End` to distinguish composition from pointwise multiplication.

These are the field-period identities used in the Ree fixed-point
construction of Aschbacher–Smith, Remark A.2.4 (`refs/quasithin.pdf`),
with the field automorphism convention of GLS, Theorem 1.15.4(a).
-/

public section

namespace ReeF4

open Theory.AlgebraicGroup

/-- Entrywise Frobenius in the monoid whose multiplication is composition. -/
@[expose] noncomputable def splitFrobeniusEnd (m : ℕ) : Monoid.End (SplitGroup m) :=
  splitFrobenius m

@[simp] theorem splitFrobeniusEnd_apply (m : ℕ) (x : SplitGroup m) :
    splitFrobeniusEnd m x = splitFrobenius m x := rfl

/-- Iterated entrywise Frobenius raises each entry to the corresponding power. -/
theorem splitFrobenius_pow_entry (m n : ℕ) (x : SplitGroup m)
    (i j : F4Chevalley.BasisIndex) :
    (((splitFrobeniusEnd m ^ n) x).val : MatrixCarrier m) i j =
      (x.val : MatrixCarrier m) i j ^ (2 ^ n) := by
  induction n with
  | zero => simp only [pow_zero, Monoid.End.coe_one, id_eq, pow_one]
  | succ n ih =>
      rw [pow_succ']
      change ((splitFrobenius m
        ((splitFrobeniusEnd m ^ n) x)).val : MatrixCarrier m) i j = _
      rw [splitFrobenius_entry, ih, ← pow_mul, ← pow_succ]

/-- The field degree is a period of Frobenius on the concrete matrix group. -/
theorem splitFrobenius_pow_fieldDegree (m : ℕ) :
    splitFrobeniusEnd m ^ (2 * m + 1) = 1 := by
  apply Monoid.End.ext
  intro x
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact (splitFrobenius_pow_entry m (2 * m + 1) x i j).trans (field_pow m _)

end ReeF4

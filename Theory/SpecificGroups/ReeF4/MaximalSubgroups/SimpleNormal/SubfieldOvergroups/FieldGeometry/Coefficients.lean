module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.FieldMaps

/-!
# Recognition of the smaller coefficient field

The image of a finite coefficient-field embedding is exactly the root set of
`X^(2^(2*k+1)) - X`. The proof counts the embedded roots against the polynomial
degree; it applies to every embedding, without choosing a preferred subfield.

This is the coefficient step in the standard subfield construction used by
Malle, J. Algebra 139 (1991), 52–69.
-/

public section

open ReeF4 ReeF4.Subfield
open Polynomial

namespace ReeF4.Subfield

/-- Membership in the embedded coefficient field is the Frobenius fixed equation. -/
theorem coefficient_mem_range_iff {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) (a : CoefficientField m) :
    a ∈ Set.range f ↔ a ^ (2 ^ (2 * k + 1)) = a := by
  classical
  let S := Finset.univ.image f
  have hp : 1 < 2 ^ (2 * k + 1) := Nat.one_lt_pow (by omega) (by omega)
  have he : (X ^ (2 ^ (2 * k + 1)) - X : (CoefficientField m)[X]).roots = S.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero
    · intro x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      simp only [eval_sub, eval_pow, eval_X, sub_eq_zero, ← map_pow, field_pow]
    · rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hp]
      dsimp [S]
      rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ,
        ← Nat.card_eq_fintype_card, field_card]
    · exact FiniteField.X_pow_card_sub_X_ne_zero _ hp
  have hm : a ∈ S ↔ a ∈ Set.range f := by simp [S]
  rw [← hm]
  change a ∈ S.val ↔ _
  rw [← he, mem_roots
    (FiniteField.X_pow_card_sub_X_ne_zero _ hp)]
  simp only [IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]

end ReeF4.Subfield

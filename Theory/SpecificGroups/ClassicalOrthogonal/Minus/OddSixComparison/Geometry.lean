module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Geometry.Descent
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Quotient

/-!
# Existence of the signed minus-six exterior realization

For an original finite field F of order pⁿ, the actual quadratic extension
and its pⁿ-Frobenius carry a signed exterior realization on the independently
constructed minus-six quadratic space. All coordinate, field, and descent
premises are discharged by the imported construction. The existing exterior
kernel theorem applies to this action and gives exactly the scalar signs.

This supplies the geometric input to the odd minus-six/unitary-four
comparison used in Aschbacher–Smith A.2.17, printed pp.38–39; see GLS3
§2.7. The independent projective-image theorem and the final group comparison
consume this witness separately.
-/

public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison
variable (p n : ℕ) [Fact p.Prime] [NeZero n]
variable (F : Type) [Field F] [Finite F] (hcard : Nat.card F = p ^ n)

include hcard in
/-- The original minus-six form admits the prescribed signed exterior realization. -/
theorem exists_signedExteriorRealization (_hp : p ≠ 2) :
    ∃ R : ExteriorRealization F (Extension p n) (unitaryForm p n),
      Nonempty (SignedCoordinates R) :=
  ⟨Geometry.realization p n F hcard, ⟨Geometry.signedCoordinates p n F hcard⟩⟩

/-- Application of exterior scalar rigidity to the action just constructed. -/
theorem Geometry.orthogonalAction_eq_one_iff (g : Geometry.SU p n) :
    Geometry.orthogonalAction p n F hcard g = 1 ↔
      ∃ a : Extension p n, a ^ 2 = 1 ∧ g.val.val = a • 1 :=
  (Geometry.realization p n F hcard).action_eq_one_iff g

/-- The kernel consists of the scalar signs, which are distinct in odd characteristic. -/
theorem Geometry.orthogonalAction_eq_one_iff_sign (g : Geometry.SU p n) :
    Geometry.orthogonalAction p n F hcard g = 1 ↔ g.val.val = 1 ∨ g.val.val = -1 := by
  rw [Geometry.orthogonalAction_eq_one_iff]
  constructor
  · rintro ⟨a, ha, hg⟩
    rcases sq_eq_one_iff.mp ha with h | h
    · exact Or.inl (by simpa [h] using hg)
    · exact Or.inr (by simpa [h] using hg)
  · rintro (h | h)
    · exact ⟨1, by simp, by simpa using h⟩
    · exact ⟨-1, by norm_num, by simpa using h⟩

end ClassicalOrthogonal.Minus.OddSixComparison

module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Reduction

/-!
# Conjugacy transport for the Held involution enumeration

The two alternatives are conjugacy to the literal representatives `a` and
`max5First ^ 4`. They are stable under further conjugation in the actual Held
carrier. This elementary transport lets a finite conjugation forest reduce
the involutions of a fixed two-subgroup to a smaller list of words.

Source: GLS3 Table 5.3p and its interpretation on printed pp.260–261.
The definitions and transport below assert no exhaustive classification.
-/

@[expose] public section

namespace Held.InvolutionFixedData.Coverage

/-- Membership in one of the two specified Held conjugacy classes. -/
def IsCovered (g : He) : Prop :=
  (∃ c : He, MulAut.conj c a = g) ∨
    (∃ c : He, MulAut.conj c (TwoLocalCandidates.max5First ^ 4) = g)

/-- A conjugation forest may transport either of the two alternatives. -/
theorem IsCovered.conj {g : He} (h : IsCovered g) (d : He) :
    IsCovered (MulAut.conj d g) := by
  rcases h with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact Or.inl ⟨d * c, by rw [map_mul]; rfl⟩
  · exact Or.inr ⟨d * c, by rw [map_mul]; rfl⟩

end Held.InvolutionFixedData.Coverage

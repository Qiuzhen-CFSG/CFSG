module

public import CFSG.KnownSimple.ClassicalModels
public import Theory.SpecificGroups.ClassicalUnitary.OddRankOneComparison

/-!
# The rank-one unitary catalogue alias

Every PSU₂(q) witness gives a PSL₂(q) witness over the fixed subfield of its
stored Hermitian conjugation. The coefficient field has order q² and the
conjugation is x ↦ x^q; these hypotheses prove that the fixed field has order q.
The even and odd matrix comparisons both descend through the literal
projective kernels. This includes all prime powers, independently of simplicity.

Source: Huppert II.10.4 and GLS III, §2.7, with the concrete comparisons in
`Theory.SpecificGroups.ClassicalUnitary.OddRankOneComparison` and
`Theory.SpecificGroups.ClassicalUnitary.TheoremDRootNormalizer.BinaryForms`.
-/

public section

namespace ClassicalGroup
variable {S : Type*} [Group S] {q : ℕ}

private theorem charTwo_of_even_card {K : Type*} [Field K] [Finite K]
    (h : Even (Nat.card K)) : CharP K 2 := by
  let : Fintype K := Fintype.ofFinite K
  apply ringChar.of_eq
  apply FiniteField.even_card_iff_char_two.mpr
  rw [← Nat.card_eq_fintype_card]
  exact Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp h)

/-- Every rank-one unitary catalogue model is a linear model at the same q. -/
theorem IsPSU.isPSL_two (hS : IsPSU S 2 q) (hq : IsPrimePow q) : ClassicalGroup.IsPSL S 2 q := by
  obtain ⟨F, _, _, J, hc, hj, ⟨e⟩⟩ := hS
  have hk := J.fixed_card_prime_power hq hc hj
  have he : Nonempty (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (FixedBy.subfield F J.conj)) := by
    rcases Nat.even_or_odd q with ho | ho
    · let : CharP F 2 := charTwo_of_even_card (hc.symm ▸ ho.pow_of_ne_zero (by decide))
      exact Theory.SpecificGroups.UnitaryRootNormalizer.nonempty_projectiveTwoEquiv J hc hk
    · exact J.nonempty_projectiveTwoEquiv_odd hq ho hc hj
  obtain ⟨ep⟩ := he
  exact ⟨FixedBy.subfield F J.conj, inferInstance, inferInstance, hk, ⟨e.trans ep⟩⟩

end ClassicalGroup

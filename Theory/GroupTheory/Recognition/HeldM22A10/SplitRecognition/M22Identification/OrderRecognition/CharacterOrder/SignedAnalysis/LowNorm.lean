module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.IntegralExpansion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SuzukiReduction

/-!
# The low-norm steps of Janko's multiplicity argument

An integral vector of squared norm at most three has only zero or unit
coordinates. Removing the principal constituent gives this bound for the third
induction as well. The only nonunit pattern of norm five has two constituents,
with multiplicities of absolute values two and one. Suzuki's fifth identity
excludes that pattern for the fifth induction.

This proves Lemma 11 for the first, second, third and fifth inductions. The
fourth induction still requires its separate source argument on p.13.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 11, pp.12–13.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G]

namespace SignedAnalysis

/-- Integer coordinates of squared norm at most three are zero or units. -/
public theorem int_unit_of_sq_le_three (a : ℤ) (ha : a ^ 2 ≤ 3) :
    a = 0 ∨ a = 1 ∨ a = -1 := by
  have hlo : -1 ≤ a := by
    by_contra h
    have : a ≤ -2 := by omega
    nlinarith
  have hhi : a ≤ 1 := by
    by_contra h
    have : 2 ≤ a := by omega
    nlinarith
  omega

/-- The only nonunit pattern of squared norm five is one coefficient of
absolute value two and one coefficient of absolute value one. -/
public theorem norm_five_nonunit_support_two {J : Type*} [Fintype J]
    (a : J → ℤ) (hn : ∑ j, a j ^ 2 = 5) (p : J)
    (hp : ¬ (a p = 0 ∨ a p = 1 ∨ a p = -1)) :
    ∃ q, q ≠ p ∧ (a q = 1 ∨ a q = -1) ∧ (a p = 2 ∨ a p = -2) ∧
      ∀ j, j ≠ p → j ≠ q → a j = 0 := by
  classical
  have hpbound : a p ^ 2 ≤ 5 := hn ▸
    Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ p)
  have hp2 : a p = 2 ∨ a p = -2 := by
    have hlo : -2 ≤ a p := by
      by_contra h
      have : a p ≤ -3 := by omega
      nlinarith
    have hhi : a p ≤ 2 := by
      by_contra h
      have : 3 ≤ a p := by omega
      nlinarith
    omega
  have hpsq : a p ^ 2 = 4 := by rcases hp2 with h | h <;> simp [h]
  let S := Finset.univ.erase p
  have hs : ∑ j ∈ S, a j ^ 2 = 1 := by
    have hh := Finset.sum_erase_add Finset.univ (fun j => a j ^ 2) (Finset.mem_univ p)
    rw [hn, hpsq] at hh
    dsimp [S]
    omega
  obtain ⟨q, hqS, hq⟩ : ∃ q ∈ S, a q ≠ 0 := by
    by_contra h
    have hz : ∀ q ∈ S, a q = 0 := by simpa using h
    have hh : ∑ j ∈ S, a j ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [hz j hj]
    omega
  have hqbound : a q ^ 2 ≤ 1 := hs ▸
    Finset.single_le_sum (fun j _ => sq_nonneg (a j)) hqS
  have hqunit : a q = 1 ∨ a q = -1 :=
    (int_unit_of_sq_le_three (a q) (by omega)).resolve_left hq
  have hqsq : a q ^ 2 = 1 := by rcases hqunit with h | h <;> simp [h]
  refine ⟨q, Finset.ne_of_mem_erase hqS, hqunit, hp2, ?_⟩
  have hrest : ∑ j ∈ S.erase q, a j ^ 2 = 0 := by
    have hh := Finset.sum_erase_add S (fun j => a j ^ 2) hqS
    rw [hs, hqsq] at hh
    omega
  intro j hjp hjq
  have hj : j ∈ S.erase q := by simp [S, hjp, hjq]
  have hjbound : a j ^ 2 ≤ 0 := hrest ▸
    Finset.single_le_sum (fun l _ => sq_nonneg (a l)) hj
  nlinarith [sq_nonneg (a j)]

end SignedAnalysis

namespace IntegralExpansion
variable {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
  {I : SpecialInductionData D k} (E : IntegralExpansion I)

/-- Removing the principal constituent leaves norm three in the third induction. -/
public theorem third_nonprincipal_norm :
    ∑ j ∈ Finset.univ.erase E.principalIndex, E.coefficient 2 j ^ 2 = 3 := by
  classical
  have hh := Finset.sum_erase_add Finset.univ (fun j => E.coefficient 2 j ^ 2)
    (Finset.mem_univ E.principalIndex)
  have hn : ∑ j, E.coefficient 2 j ^ 2 = 4 := E.norm_sq 2
  have hp : E.coefficient 2 E.principalIndex = 1 := E.principal_coefficient 2
  rw [hn, hp] at hh
  norm_num only [one_pow] at hh
  omega

public theorem first_three_unit (i : Fin 5) (hi : i < 3) (j : E.Index) :
    E.coefficient i j = 0 ∨ E.coefficient i j = 1 ∨ E.coefficient i j = -1 := by
  classical
  fin_cases i
  · exact SignedAnalysis.int_unit_of_sq_le_three _ (E.coefficient_sq_le 0 j)
  · exact SignedAnalysis.int_unit_of_sq_le_three _ (E.coefficient_sq_le 1 j)
  · by_cases hj : j = E.principalIndex
    · subst j
      rw [E.principal_coefficient]
      norm_num [exceptionalCoefficients]
    · apply SignedAnalysis.int_unit_of_sq_le_three
      rw [← E.third_nonprincipal_norm]
      exact Finset.single_le_sum (fun l _ => sq_nonneg (E.coefficient 2 l))
        (by simp [hj])
  · simp at hi
  · simp at hi

public theorem fifth_unit (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (L : LocalAnalysisData D k) (I : SpecialInductionData D k)
    (hI : HasSuzukiPairings I) (E : IntegralExpansion I) (j : E.Index) :
    E.coefficient 4 j = 0 ∨ E.coefficient 4 j = 1 ∨ E.coefficient 4 j = -1 := by
  by_contra h
  obtain ⟨q, hqj, _, _, hz⟩ := SignedAnalysis.norm_five_nonunit_support_two
    (E.coefficient 4) (E.norm_sq 4) j h
  exact fifth_induction_ne_two_irreducibles D k L I hI
    (E.character j) (E.character q) (E.irreducible j) (E.irreducible q)
    (E.coefficient 4 j) (E.coefficient 4 q) (E.expansion_two 4 j q hqj.symm hz)

end IntegralExpansion

/-- The first three conclusions of Lemma 11 follow from the exact norms
and the principal multiplicity, for every ambient irreducible. -/
public theorem first_three_unit_multiplicities {D : LocalData G}
    {k : TwistedModel ≃* D.centralizer} (I : SpecialInductionData D k)
    (χ : ClassFunction G) (hχ : IsIrreducibleCharacter χ) (i : Fin 5) (hi : i < 3) :
    scalarProduct G (I.induced i) χ = 0 ∨ scalarProduct G (I.induced i) χ = 1 ∨
      scalarProduct G (I.induced i) χ = -1 := by
  obtain ⟨E⟩ := exists_integralExpansion I
  obtain ⟨j, rfl⟩ := E.complete χ hχ
  rw [E.multiplicity]
  rcases E.first_three_unit i hi j with h | h | h <;> simp [h]

/-- Lemma 11 for the fifth induction: its only possible nonunit pattern
would contradict its Suzuki pairing. -/
public theorem fifth_unit_multiplicities (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I)
    (χ : ClassFunction G) (hχ : IsIrreducibleCharacter χ) :
    scalarProduct G (I.induced 4) χ = 0 ∨ scalarProduct G (I.induced 4) χ = 1 ∨
      scalarProduct G (I.induced 4) χ = -1 := by
  obtain ⟨E⟩ := exists_integralExpansion I
  obtain ⟨j, rfl⟩ := E.complete χ hχ
  rw [E.multiplicity]
  rcases E.fifth_unit D k L I hI j with h | h | h <;> simp [h]
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder

module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.Small
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.Denominator
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeConstraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeXYArithmetic
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeZArithmetic

/-!
# Janko's second character decomposition

The second decomposition forces the ambient order to be 443520. If all three
ratios at indices 0, 3 and 5 are at most one quarter, `CaseTwo.Small` gives
the inclusive cofactor bound and exhausts every cofactor, including 1 and 55.
Otherwise, the actual characters give the integer system in
`CaseTwo.LargeConstraints`. The complete large-X/Y exhaustion leaves the
desired order and two patterns excluded by the second character's degree and
value relations; the complete large-Z exhaustion gives a contradiction.
All signs and both free multiplicities are retained throughout, including
the minus sign on constituent 3 in the third decomposition equation.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
open LocalModelDichotomy

noncomputable section
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- Janko's second decomposition has order 443520 in every ratio regime. -/
public theorem card_eq_443520_caseTwo [IsSimpleGroup G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I)
    (hu : HasUnitMultiplicities I.induced) (F : SignedFamily G 6)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (h3 : I.induced 2 = 1 + F.term 0 - F.term 3 + F.term 5) :
    Nat.card G = 443520 := by
  have S := caseTwo_integerSystem D k L I hI hu F h1 h2 h3
  by_cases hxy : 1/4 < involutionRatio I (F.irreducible 0) ∨
      1/4 < involutionRatio I (F.irreducible 3)
  · have hb : ((caseTwoSignedDegree F 0).natAbs : ℤ) <
        4 * (caseTwoSignedValue I F 0)^2 ∨
        ((caseTwoSignedDegree F 3).natAbs : ℤ) <
        4 * (caseTwoSignedValue I F 3)^2 :=
      hxy.elim
        (fun h => Or.inl (caseTwo_large_degree_bound I F 0 h))
        (fun h => Or.inr (caseTwo_large_degree_bound I F 3 h))
    rcases caseTwo_largeXY_candidates S hb with hg | ⟨hg, hx, hy⟩ | ⟨ha, hb⟩
    · exact hg
    · exact (caseTwo_exclude_degree_pattern I F h1 h2 hg hx hy).elim
    · exact (caseTwo_exclude_value_pattern D k L I hu F h1 h2 h3 ha hb).elim
  · have hr0 : involutionRatio I (F.irreducible 0) ≤ 1/4 :=
      le_of_not_gt (fun h => hxy (Or.inl h))
    have hr3 : involutionRatio I (F.irreducible 3) ≤ 1/4 :=
      le_of_not_gt (fun h => hxy (Or.inr h))
    by_cases hr5 : involutionRatio I (F.irreducible 5) ≤ 1/4
    · exact card_eq_443520_caseTwo_small D k L I hI hu F h1 h2 h3 hr0 hr3 hr5
    · exact (caseTwo_largeZ_impossible S
        (caseTwo_large_degree_bound I F 5 (lt_of_not_ge hr5))).elim

end
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion

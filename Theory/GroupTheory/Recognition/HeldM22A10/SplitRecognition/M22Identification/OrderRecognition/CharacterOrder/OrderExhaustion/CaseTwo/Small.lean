module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.Rows
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.SmallArithmetic

/-!
# Bounded cofactors in Janko's second decomposition

The actual signed rows satisfy the finite integer constraints in
`SmallArithmetic`. That exhaustive computation leaves only cofactor eleven,
using the genuine degree divisibility, Sylow restriction congruence, and third
Suzuki equation. In particular it treats both endpoints one and fifty-five.
The small-ratio theorem supplies the required bound without any new premise.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
open LocalModelDichotomy
noncomputable section
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- Each of the six actual signed rows satisfies its arithmetic conditions. -/
public theorem caseTwo_signedRow_conditions (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hu : HasUnitMultiplicities I.induced)
    (F : SignedFamily G 6)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (h3 : I.induced 2 = 1 + F.term 0 - F.term 3 + F.term 5) (j : Fin 6) :
    CaseTwoRowConditions (Nat.card G)
      (153 * caseTwoBase j 0 - 202 * caseTwoBase j 1 + 127 * caseTwoBase j 2)
      (7 * caseTwoBase j 0 - 6 * caseTwoBase j 1 + caseTwoBase j 2)
      (caseTwoSignedDegree F j, caseTwoSignedValue I F j) := by
  have hc0 := caseTwo_base_multiplicities I F h1 h2 h3 j 0
  have hc1 := caseTwo_base_multiplicities I F h1 h2 h3 j 1
  have hc2 := caseTwo_base_multiplicities I F h1 h2 h3 j 2
  have hv := caseTwo_signedValue_formula I F j
  have hd := caseTwo_signedDegree_congruence L I F j
  change caseTwoSignedMultiplicity I F j 0 = caseTwoBase j 0 at hc0
  change caseTwoSignedMultiplicity I F j 1 = caseTwoBase j 1 at hc1
  change caseTwoSignedMultiplicity I F j 2 = caseTwoBase j 2 at hc2
  rw [hc0, hc1, hc2] at hv hd
  refine ⟨(caseTwo_signedDegree_dvd F j).2,
    caseTwoSignedMultiplicity I F j 3, caseTwo_signedMultiplicity_unit I hu F j 3,
    caseTwoSignedMultiplicity I F j 4, caseTwo_signedMultiplicity_unit I hu F j 4,
    hv, ?_⟩
  convert hd using 1
  ring

/-- Every bounded cofactor in the second decomposition is eleven. -/
public theorem card_eq_443520_caseTwo_of_cofactor_le55 (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I)
    (hu : HasUnitMultiplicities I.induced) (F : SignedFamily G 6)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (h3 : I.induced 2 = 1 + F.term 0 - F.term 3 + F.term 5)
    (h : ℕ) (he : Nat.card G = 40320*h) (hb : h ≤ 55) : Nat.card G = 443520 := by
  obtain ⟨h', hp, he', htwo, hthree⟩ := exists_order_cofactor D k L
  have hsame : h' = h := by omega
  subst h'
  have hrow := caseTwo_signedRow_conditions D k L I hu F h1 h2 h3
  have hpRow : CaseTwoRowConditions (40320*h) 78 2
      (caseTwoSignedDegree F 0, caseTwoSignedValue I F 0) := by
    rw [← he]
    simpa [caseTwoBase] using hrow 0
  have hqRow : CaseTwoRowConditions (40320*h) (-329) (-7)
      (caseTwoSignedDegree F 3, caseTwoSignedValue I F 3) := by
    rw [← he]
    simpa [caseTwoBase] using hrow 3
  have hrRow : CaseTwoRowConditions (40320*h) 127 1
      (caseTwoSignedDegree F 5, caseTwoSignedValue I F 5) := by
    rw [← he]
    simpa [caseTwoBase] using hrow 5
  have hs := caseTwo_third_suzuki_int D k L I hI F h3
  dsimp only at hs
  rw [he] at hs
  have hh := caseTwo_small_integer_exhaustion h hp htwo hthree hb _ _ _ hpRow hqRow hrRow
    (caseTwo_third_degree I F h3) (caseTwo_third_value I F h3) hs
  rw [he, hh]

/-- The whole small-ratio regime of the second decomposition has the M22 order. -/
public theorem card_eq_443520_caseTwo_small (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I)
    (hu : HasUnitMultiplicities I.induced) (F : SignedFamily G 6)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (h3 : I.induced 2 = 1 + F.term 0 - F.term 3 + F.term 5)
    (hr0 : involutionRatio I (F.irreducible 0) ≤ 1/4)
    (hr3 : involutionRatio I (F.irreducible 3) ≤ 1/4)
    (hr5 : involutionRatio I (F.irreducible 5) ≤ 1/4) : Nat.card G = 443520 := by
  obtain ⟨h, _, he, _, _, hb⟩ := caseTwo_smallRatio_cofactor D k L I hI F h3 hr0 hr3 hr5
  exact card_eq_443520_caseTwo_of_cofactor_le55 D k L I hI hu F h1 h2 h3 h he hb

end
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion

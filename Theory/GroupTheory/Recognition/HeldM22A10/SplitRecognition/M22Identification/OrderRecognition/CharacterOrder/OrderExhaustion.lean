module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.Boundary
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SuzukiReduction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseOneSmall
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseOneLarge
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo

/-!
# The M22 order from the character analysis

The local subgroup factorization, the actual Sylow restriction congruence,
and the rational Suzuki reductions in `Constraints` supply the three exhaustive
branch theorems. In the first signed decomposition, either one of the three
ratios exceeds one quarter or all three satisfy the printed non-strict bound.
The second decomposition already includes both ratio regimes, with its minus
sign preserved. Thus both alternatives force `Nat.card G = 443520`.

The small-ratio calculations cover every cofactor up to and including 55,
including the degree obstruction at cofactor 1. The large-ratio calculations
prove completeness for every selected constituent, sign, and pair of final
multiplicities. Their arithmetic premises are derived from the actual supplied
characters and local subgroups; no further certificate is assumed here.

Construction of the special inductions, Suzuki pairings, unit multiplicities,
and signed decomposition remains with their independent producers. This theorem
takes precisely those character inputs explicitly, leaving their discharge to
the ambient-order theorem from `LocalAnalysisData` alone.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy OrderExhaustion

universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

/-- Both character decompositions force the Mathieu order. The character-analysis
inputs are explicit; every arithmetic branch is discharged by the local data. -/
public theorem card_eq_443520_of_characterAnalysis (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I)
    (hu : HasUnitMultiplicities I.induced) (hd : HasJankoDecomposition I.induced) :
    Nat.card G = 443520 := by
  rcases hd with ⟨F, h0, h1, h2⟩ | ⟨F, h0, h1, h2⟩
  · by_cases hr : 1/4 < involutionRatio I (F.irreducible 1) ∨
        1/4 < involutionRatio I (F.irreducible 5) ∨
        1/4 < involutionRatio I (F.irreducible 6)
    · exact card_eq_443520_caseOne_large D k L I hI hu F h0 h1 h2 hr
    · exact card_eq_443520_caseOne_small D k L I hI hu F h0 h1 h2
        (le_of_not_gt (fun h => hr (Or.inl h)))
        (le_of_not_gt (fun h => hr (Or.inr (Or.inl h))))
        (le_of_not_gt (fun h => hr (Or.inr (Or.inr h))))
  · exact card_eq_443520_caseTwo D k L I hI hu F h0 h1 h2

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder

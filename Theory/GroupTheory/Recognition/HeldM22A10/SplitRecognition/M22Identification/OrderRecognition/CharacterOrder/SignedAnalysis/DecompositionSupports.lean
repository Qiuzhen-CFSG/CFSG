module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.DecompositionSupports.Third
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.RejectedDecomposition

/-!
# Janko's signed decomposition, conditional on unit multiplicities

The complete integral expansions construct the first two three-term supports.
Their common constituent is unique: a three-constituent overlap would contradict
the degree-zero equations and nonzero irreducible degrees. After removing the
principal constituent from the third induction, the Gram equations exhaust its
support into the two source alternatives or one five-character pattern. The
existing Suzuki-pairing argument excludes that last pattern.

All witnesses are actual, distinct, nonprincipal irreducible characters, with
all signs retained. Unit multiplicities are an explicit input (Lemma 11); their
proof and the unconditional assembly remain with the parent signed analysis.
No ambient-order or identification premise is used.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 12, pp.13–14.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
namespace SignedAnalysis
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Janko's two signed decompositions from the local data, actual Suzuki
pairings, and the separately supplied unit-multiplicity conclusion. -/
public theorem has_janko_decomposition_of_unit_multiplicities
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I)
    (hU : HasUnitMultiplicities I.induced) : HasJankoDecomposition I.induced := by
  obtain ⟨E⟩ := exists_integralExpansion I
  rcases DecompositionSupports.alternatives_or_rejected E hU with h | ⟨F, he0, he1, he2⟩
  · exact h
  · exact (rejected_decomposition_impossible D k L I hI hU F he0 he1 he2).elim

end SignedAnalysis
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder

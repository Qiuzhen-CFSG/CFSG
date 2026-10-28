module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.Boundary
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SuzukiReduction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.LowNorm
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.FourthArithmetic
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.RejectedDecomposition
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.FourthMultiplicity
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.DecompositionSupports

/-!
# Signed multiplicities and decompositions in Janko's exceptional inductions

The actual five induced class functions admit simultaneous integral expansions
in the complete ordinary irreducible basis. Orthogonality transfers their Gram
matrix to integer coordinates. Their norms, principal coefficient and fifth
Suzuki pairing prove unit multiplicities for the first, second, third and fifth
inductions. For the fourth, positivity of the remaining squared norms reduces
the nonunit case to two patterns. Their actual Suzuki equations contradict the
Sylow three-order or an integer quadratic modulo nine, completing Lemma 11.

These unit multiplicities construct distinct signed nonprincipal constituents
and exhaust the third induction into the two source alternatives or a rejected
pattern. The latter is excluded using its actual Gram and Suzuki equations, E16
restriction, and ordinary character-degree divisibility. Both involution values
and all four signed differences on p.14 are retained, completing Lemma 12.

The theorem below discharges the unit-multiplicity premise of the decomposition
argument. Its remaining inputs are precisely the local analysis, actual
normalizer inductions, and Suzuki pairings. Constructing these inputs belongs to
the ambient-order assembly; no ambient order or identification is assumed here.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemmas 11–12, pp.12–14.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
namespace SignedAnalysis
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Janko's Lemmas 11–12 for the actual exceptional inductions: every
irreducible multiplicity is zero or a unit, and the first three inductions have
one of the two signed decompositions. The local analysis, induction data, and
Suzuki pairings remain explicit inputs to the character argument. -/
public theorem unit_multiplicities_and_janko_decomposition
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I) :
    HasUnitMultiplicities I.induced ∧ HasJankoDecomposition I.induced := by
  have hU := hasUnitMultiplicities D k L I hI
  exact ⟨hU, has_janko_decomposition_of_unit_multiplicities D k L I hI hU⟩

end SignedAnalysis
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder

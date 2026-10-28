module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.Boundary
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SuzukiReduction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ModelPairCounts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SuzukiPairings
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis

/-!
# The character calculation for the M22 order

`card_eq_443520_of_localAnalysis` proves the ambient order from the actual
Case II centralizer identification and `LocalAnalysisData`. The normalizer
character construction supplies the five special inductions; their actual
involution-pair scalar products give the Suzuki identities. The signed analysis
then proves unit multiplicities and both decomposition alternatives, discharging
every character premise of `card_eq_443520_of_characterAnalysis`.

Both decomposition cases and every small- and large-ratio branch are exhausted,
including the cofactors 1 and 55. Equality at the one-quarter ratio boundary is
excluded using the actual E16 and Sylow two-subgroup. Constructing the centralizer
identification and local analysis remains the preceding group-theoretic argument.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 6–7, pp.11–15,
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy CharacterOrder

universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

/-- Janko's Lemma 14: the Case II local analysis forces the Mathieu order.
All normalizer characters, special inductions, Suzuki pairings and signed
decompositions used by the order exhaustion are constructed from `D`, `k`, `L`. -/
public theorem card_eq_443520_of_localAnalysis (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k) :
    Nat.card G = 443520 := by
  obtain ⟨I⟩ := nonempty_specialInductionData D k L
  have hI := hasSuzukiPairings_of_localAnalysis D k L I
  obtain ⟨hu, hd⟩ := SignedAnalysis.unit_multiplicities_and_janko_decomposition D k L I hI
  exact card_eq_443520_of_characterAnalysis D k L I hI hu hd

end Theory.GroupTheory.HeldM22A10.M22Identification

module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Elementary
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ElementCentralizers
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.FourFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ClassDistributions

/-!
# Janko's Case II local analysis

The two source elementary subgroups, their ambient self-centralizers and
the centralizer orders of the four noninvolutory representatives are proved
in the imported modules. The two order-four classes are distinct, and their
coverage follows from ambient involution fusion.

For a finite simple ambient group, the actual normalizer complements and
involution fusion supply the three-local conclusions. Those conclusions
then supply the order-three fusion needed for both ambient class
distributions. `localAnalysisData_of_caseII` assembles all these results
from the original local data and the Case II centralizer equivalence.
The Sylow distribution uses the original `D.sylow`, and the three-normalizer
order retains both 72 and 144.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1–19, Sections 2–5 and Lemma 13.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u

/-- Assemble the proved coordinate calculations with the remaining local
conclusions. This does not discharge the three explicit intermediate premises. -/
public theorem localAnalysisData_of_local_conclusions {G : Type u} [Group G] [Finite G]
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (h2 : InvolutionNormalizerData D k) (h3 : ThreeLocalData D k)
    (hd : LocalClassDistributions D k) : LocalAnalysisData D k where
  E_elementary := CaseII.E_elementary D k
  E_card := CaseII.E_card D k
  E_centralizer := CaseII.E_centralizer D k
  F_elementary := CaseII.F_elementary D k
  F_card := CaseII.F_card D k
  F_centralizer := CaseII.F_centralizer D k
  normalizer_E := h2.normalizer_E
  normalizer_F := h2.normalizer_F
  involution_fusion := h2.involution_fusion
  three_fusion := h3.three_fusion
  sylow_three := h3.sylow_three
  normalizer_three := h3.normalizer_three
  nonabelian_twenty_one := h3.nonabelian_twenty_one
  four_fusion := CaseII.four_fusion_of_involution_fusion D k h2.involution_fusion
  four_not_fused := CaseII.four_not_fused D k
  centralizer_orders := CaseII.centralizer_orders D k
  centralizer_distribution := hd.centralizer_distribution
  sylow_distribution := hd.sylow_distribution

/-- Janko's selected local conclusions for Case II, with every intermediate
normalizer, fusion and counting premise discharged. The supplied centralizer
equivalence is arbitrary and need not mark the original Sylow subgroup. -/
public theorem localAnalysisData_of_caseII {G : Type u} [Group G] [Finite G]
    [IsSimpleGroup G] (D : LocalData G) (k : TwistedModel ≃* D.centralizer) :
    LocalAnalysisData D k := by
  have h2 := involutionNormalizerData_of_caseII D k
  have h3 := threeLocalData_of_involution_normalizers D k h2
  exact localAnalysisData_of_local_conclusions D k h2 h3
    (localClassDistributions_of_involution_normalizers D k h2 h3.three_fusion)

end Theory.GroupTheory.HeldM22A10.M22Identification

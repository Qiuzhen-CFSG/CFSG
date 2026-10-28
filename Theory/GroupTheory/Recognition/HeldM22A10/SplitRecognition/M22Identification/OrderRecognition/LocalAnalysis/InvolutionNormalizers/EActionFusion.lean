module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.Interfaces
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.NormalizerAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.CentralizerFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.ActorCentralizers
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.QuotientAlternatives
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion

/-!
# Janko's A6 normalizer action and actor fusion

Fusion of the marked involution with printed z₃ restricts the literal
quotient N(E)/E to order 168 or an actual A6 model. The order-168 branch
forces actor fusion; the supplied F-normalizer implication then gives an
S5 quotient incompatible with its intersection action on E. The surviving
A6 quotient forces the orbit on E to have size fifteen.

Under contrary actor nonfusion, `ActorCentralizers` now puts the full
centralizer of every involution of N(E) inside N(E). The elementary
dihedral argument contradicts nonfusion. Thus the final theorem constructs
the E-normalizer action and fuses d using only the two earlier source inputs
`hz3` and `hF`. Their construction and the global splitting clauses remain
with the full involution-normalizer assembly.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemmas 6–7, pp.5–7.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
  (D : LocalData G) (k : TwistedModel ≃* D.centralizer)

/-- Conditional assembly; neither the A6 identification nor the centralizer
containment is asserted without its explicit premise. -/
public theorem eNormalizerAction_and_actorFusion_of_quotient_and_centralizers
    (hq : Nonempty (CaseII.eNormalizerQuotient D k ≃* alternatingGroup (Fin 6)))
    (hC : ¬ IsConj D.z (CaseII.into D k CaseII.d) →
      ∀ t ∈ normalizer (CaseII.E D k : Set G), orderOf t = 2 →
        centralizer ({t} : Set G) ≤ normalizer (CaseII.E D k : Set G)) :
    ENormalizerAction D k ∧ IsConj D.z (CaseII.into D k CaseII.d) := by
  refine ⟨CaseII.eNormalizerAction_of_quotient D k hq, ?_⟩
  by_contra hn
  apply hn
  apply CaseII.involution_fusion_of_E_centralizer_closure D k (hC hn)
  rw [orderOf_injective (CaseII.into D k) (CaseII.into_injective D k)]
  exact CaseII.actor_orders.2.2.2

/-- The automizer and actor-fusion conclusions of Janko's Lemmas 6–7,
from the initial fusion of Lemma 5 and the F-normalizer implication of
Lemma 2. The quotient alternatives, order-168 exclusion and centralizer
containment are all discharged here; global splitting is separate. -/
public theorem eNormalizerAction_and_actorFusion
    (hz3 : IsConj D.z (CaseII.into D k (CaseII.z 2)))
    (hF : IsConj D.z (CaseII.into D k CaseII.d) → FNormalizerAction D k) :
    ENormalizerAction D k ∧ IsConj D.z (CaseII.into D k CaseII.d) := by
  rcases eNormalizerQuotient_alternatives D k hz3 with h168 | hq
  · exact (l27_exclusion D k hz3 hF h168).elim
  · exact eNormalizerAction_and_actorFusion_of_quotient_and_centralizers D k hq
      (eNormalizer_involution_centralizers_of_actor_nonfusion D k
        (CaseII.eNormalizerAction_of_quotient D k hq))

end Theory.GroupTheory.HeldM22A10.M22Identification

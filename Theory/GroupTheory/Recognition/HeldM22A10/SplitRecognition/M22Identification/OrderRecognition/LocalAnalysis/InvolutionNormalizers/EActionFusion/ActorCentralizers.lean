module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.Interfaces
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.NormalizerAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.CentralizerFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.ActorCentralizers.FOrder

/-!
# Centralizer containment under contrary actor nonfusion

Assume the actual A6 quotient and transitive action of N(E), but that z and
d are not conjugate in G. Quotient conjugacy and the coordinate action show
that every involution of N(E) outside E is conjugate to a within N(E).
Normalizer control makes U = C(a) ∩ C(z) Sylow in C(a); its marked central
involution is weakly closed, and the elementary four E ∩ U forces the odd
core of C(a) to vanish. The core-free Z-star theorem gives C(a) = U.
Conjugating these centralizers within N(E) gives the required containment.

The descendants also establish |N(F)/F| = 24 from these hypotheses. The
Sylow normalizer argument lets us obtain C(a) first, without assuming that
order calculation or a global splitting. Every extra premise of this
conditional helper is displayed; the recognition owner constructs the
normalizer action and discharges actor nonfusion by contradiction.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 7, p.7, and the C(a) analysis on p.6.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G]
  (D : LocalData G) (k : TwistedModel ≃* D.centralizer)

/-- Under contrary actor nonfusion, N(E) contains the full ambient
centralizer of each of its involutions. -/
public theorem eNormalizer_involution_centralizers_of_actor_nonfusion [IsSimpleGroup G]
    (hE : ENormalizerAction D k) (hn : ¬ IsConj D.z (CaseII.into D k CaseII.d)) :
    ∀ t ∈ normalizer (CaseII.E D k : Set G), orderOf t = 2 →
      centralizer ({t} : Set G) ≤ normalizer (CaseII.E D k : Set G) := by
  apply CaseII.E_centralizer_closure_of_actor_a D k hE
  rw [CaseII.actorCentralizer_eq_local D k hE hn]
  exact CaseII.actorLocalCentralizer_le_normalizer_E D k

end Theory.GroupTheory.HeldM22A10.M22Identification

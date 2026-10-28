module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.InitialS.Complete
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.XiFusion.SNormalizerFusion.OrbitReduction

/-!
# Held's tau fusion with the original marking

The completed initial S-fusion leaves tau or one of the two lambda choices.
Lambda fusion produces a cubic normalizer of its order-32 local centralizer,
and this element normalizes S. The nine-point pi orbit then includes tau.
The permitted lambda twist fixes tau and mu, so the other lambda choice gives
exactly the same conclusion for the supplied centralizer isomorphism.

All source fusion, normalizer and marking premises are discharged from the
finite simple local data. This is the input to the actual noncentral A6
section and the subsequent A10 recognition assembly.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemmas 2.9--2.11, printed pp.229--230.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates LambdaSeparation CentralizerStructure.FaithfulExclusion
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private theorem tau_fusion_of_lambda
    (hl : IsConj D.z (D.a10ModelEmbedding e lam)) :
    IsConj D.z (D.a10ModelEmbedding e tau) := by
  obtain ⟨x, hx, hc⟩ := lambda_three_element_of_core_three D e
    (lambdaCore_three_of_not_two D e (lambdaCore_normalizer_not_two D e hl))
  obtain ⟨_, ht, _, _⟩ := exists_s_fusion_of_orbit_nine D e
    (pi_mu_nonfusion D e) (lambda_separation D e)
    (piPoint_orbit_card_of_three_centralizer D e x hx hc)
  exact ht

/-- Held's tau fusion, retaining the exact originally supplied marking. -/
public theorem tau_fusion_of_simple : IsConj D.z (D.a10ModelEmbedding e tau) := by
  rcases InitialS.initial_s_fusion D e with ht | hl | hl
  · exact ht
  · exact tau_fusion_of_lambda D e hl
  · have hl' : IsConj D.z (D.a10ModelEmbedding (twistEquiv D e) lam) := by
      rwa [twistEquiv_lam]
    have ht := tau_fusion_of_lambda D (twistEquiv D e) hl'
    rw [twistEquiv_embedding, show lambdaTwist tau = tau from lambdaTwist_generators 3] at ht
    exact ht

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion

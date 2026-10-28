module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.Tables
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.SylowActor
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.ActionContradiction

/-!
# Additional fusion forced by pi--mu fusion

If pi is conjugate to mu and is not conjugate to lambda, at least one of
tau, pi*lambda, xi, pi*xi and tau*lambda*xi is conjugate to pi.

Supposing all five are excluded, the elementary-subgroup catalogue makes M
weakly closed in the displayed Sylow subgroup. A Sylow subgroup of C_G(mu)
containing the common order-64 intersection then supplies an order-three
element normalizing M and cycling pi, mu and pi*mu. The normalizer-action
argument gives a pi orbit of size seven, |N_G(M)| = 384*7, and a faithful
N_G(M)/M action on the even flips. The xi orbit has size four; an element
of order seven in its stabilizer must fix all four xi conjugates generating
M. Self-centralization puts this element in M of order sixteen, a contradiction.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, first paragraph of Lemma 2.6, p.228.
The source convention x^g is g^-1*x*g.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates
universe u

/-- The additional fused representative forced by pi--mu fusion, with lambda separated.
Both the order-three actor and the normalizer-action contradiction are derived
from these hypotheses and the negation of the five alternatives. -/
public theorem additional_fusion_of_mu {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (D : LocalData G) (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam)) :
    IsConj D.z (D.a10ModelEmbedding e tau) ∨
    IsConj D.z (D.a10ModelEmbedding e (pi * lam)) ∨
    IsConj D.z (D.a10ModelEmbedding e xi) ∨
    IsConj D.z (D.a10ModelEmbedding e (pi * xi)) ∨
    IsConj D.z (D.a10ModelEmbedding e (tau * lam * xi)) := by
  by_contra! h
  obtain ⟨htau, hpl, hxi, hpx, htlx⟩ := h
  have hno : NoAdditionalFusion D e := by
    intro i
    fin_cases i
    · exact htau
    · exact hpl
    · exact hxi
    · exact hpx
    · exact htlx
  obtain ⟨v, hvN, hv3, hvpi, hvmu⟩ := exists_mu_three_actor D e hmu hlam hno
  exact additional_fusion_contradiction_of_three_actor D e hmu hlam hno v hvN hv3 hvpi hvmu

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion

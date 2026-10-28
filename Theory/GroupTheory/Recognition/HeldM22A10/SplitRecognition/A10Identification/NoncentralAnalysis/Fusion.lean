module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Normalization
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Geometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LocalSylow
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Catalogue
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.SNormalizer
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Terminal

/-!
# Held's pi--mu nonfusion theorem

The specified involutions pi and mu are not conjugate in the ambient finite
simple group. Lemma 2.4 and the genuine whole-centralizer change of lambda
first give normalized coordinates preserving the original mu. Assuming pi--mu
fusion, the first part of Lemma 2.6 forces an additional fused representative.
The S-normalizer argument excludes tau and pi*lambda. The remaining three
alternatives give the terminal contradiction between centers of orders 8 and 4.

All normalization and branch premises are discharged. The proof uses the
actual local model, its elementary-subgroup catalogue, and the constructed
ambient normalizers and overgroups. It neither assumes the ambient centralizer
order of mu nor uses global recognition. The local prerequisite APIs remain
re-exported here.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Section 1 and Lemmas 2.4--2.6, pp.225--229.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion

universe u

/-- Held's Lemma 2.6: the original pi and mu are not conjugate in G.
The permitted lambda normalization preserves the mu specified by the supplied e. -/
public theorem pi_mu_nonfusion {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (D : LocalData G) (e : D.centralizer ≃* CentralizerModels.a10Centralizer) :
    ¬ IsConj D.z (D.a10NoncentralInvolution e) := by
  obtain ⟨e', hmu_eq, hlam⟩ := exists_normalized_equiv_of_simple D e
  intro hmu
  have hmu' : IsConj D.z (D.a10NoncentralInvolution e') := by
    rwa [hmu_eq]
  obtain ⟨htau, hpilam⟩ := tau_piLambda_nonfusion_of_mu D e' hmu' hlam
  have hadditional := additional_fusion_of_mu D e' hmu' hlam
  rcases hadditional with h | h | h
  · exact htau h
  · exact hpilam h
  · exact terminal_mu_contradiction D e' hmu' hlam htau hpilam h

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion

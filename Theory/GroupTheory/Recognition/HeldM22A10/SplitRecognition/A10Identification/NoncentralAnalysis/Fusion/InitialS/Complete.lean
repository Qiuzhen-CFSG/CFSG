module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.InitialS.Alternatives
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.InitialS.PiXiBranch.Exclusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.InitialS.CrossBranch

/-!
# Held's initial S-fusion

Z-star and the actual local involution table supply a noncentral conjugate
of pi. The proved pi--mu nonfusion removes mu. If none of tau, lambda and
pi*lambda is fused with pi, weak closure and the local centralizer comparisons
exclude both xi classes. The order-five argument on L2 excludes the final
cross representative. Thus a noncentral conjugate already lies in S.

This is Held 2.9 before choosing between lambda and pi*lambda. The following
tau module supplies the later normalizer argument without changing the marking.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemmas 2.9--2.10, printed pp.229--230.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS
open Coordinates
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- Held 2.9, with the two allowed lambda markings retained explicitly. -/
public theorem initial_s_fusion :
    IsConj D.z (D.a10ModelEmbedding e tau) ∨
      IsConj D.z (D.a10ModelEmbedding e lam) ∨
      IsConj D.z (D.a10ModelEmbedding e (pi * lam)) := by
  by_contra! hn
  have h : Separated D e := ⟨pi_mu_nonfusion D e, hn.1, hn.2.1, hn.2.2⟩
  obtain ⟨hxi, hpiXi⟩ := xi_and_piXi_nonfusion D e h
  have hcross := cross_nonfusion D e h hxi hpiXi
  rcases initial_fusion_alternatives D e with hf | hf | hf | hf | hf | hf | hf
  · exact h.1 hf
  · exact h.2.1 hf
  · exact h.2.2.1 hf
  · exact h.2.2.2 hf
  · exact hxi hf
  · exact hpiXi hf
  · exact hcross hf

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS

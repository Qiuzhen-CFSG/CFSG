module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.InitialS.PiXiBranch.Transfer
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.InitialS.Centralizers
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.XiFusion.XiSeparation

/-!
# Excluding both xi fusions in Held's initial S argument

Under the contrary initial-fusion hypothesis, the pi--pi*xi branch constructs
a cubic actor and Thompson transfer sends pi*lambda to mu or tau. Weak closure
of S makes their local centralizers Sylow; their orders and center orders
exclude both alternatives. The preceding xi-separation theorem then eliminates
both xi choices. This completes the first case of Held 2.9.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.9, printed pp.229--230.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS
open Coordinates CentralizerStructure.FaithfulExclusion
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The first contrary branch in Held 2.9 is impossible for either xi marking. -/
public theorem piXi_nonfusion (h : Separated D e) (d : Bit)
    (hxi : ¬ IsConj D.z (D.a10ModelEmbedding e (normalizedXi d))) :
    ¬ IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * normalizedXi d)) := by
  intro hpiXi
  rcases piLambda_isConj_mu_or_tau_of_piXi_fusion D e h.1 h.2.2.2 d hxi hpiXi with hf | hf
  · exact piLambda_mu_nonfusion D e h hf
  · exact piLambda_tau_nonfusion D e h hf

/-- Neither local xi class contains the distinguished involution under the
contrary S-fusion hypothesis. -/
public theorem xi_and_piXi_nonfusion (h : Separated D e) :
    ¬ IsConj D.z (D.a10ModelEmbedding e xi) ∧
      ¬ IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * xi)) := by
  have hs := xi_separation_of_nonfusion D e h.1
  have hx : ¬ IsConj D.z (D.a10ModelEmbedding e xi) := by
    intro hx
    have hpx : ¬ IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * xi)) :=
      fun hp => hs ⟨hx, hp⟩
    have hh := piXi_nonfusion D e h 1 (by simpa [normalizedXi] using hpx)
    have he : Coordinates.pi * normalizedXi 1 = xi := by decide +kernel
    rw [he] at hh
    exact hh hx
  exact ⟨hx, piXi_nonfusion D e h 0 (by simpa [normalizedXi] using hx)⟩

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS

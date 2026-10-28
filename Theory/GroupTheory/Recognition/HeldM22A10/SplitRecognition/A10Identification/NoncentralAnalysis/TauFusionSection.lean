module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.IndexFour
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.SourceFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.DihedralModels
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.Splitting
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.PSL2Seven
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.Overgroup
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.XiFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.XiFusion.XiSeparation
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu.InitialActor
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu.CrossFusion

/-!
# The noncentral A₆ section from Held's earlier τ fusion

The fusion of π with τ constructs both earlier ambient actors. Their quotient
fusion gives the normal index-four core in C_G(μ)/⟨μ⟩. Dihedral recognition and
central splitting identify its derived lift with A₆ or PSL₂(7). The compatible
actors make the proper extension by μ′ faithful, excluding PSL₂(7) by the
absence of elements of order eight. The actual quotient by the resulting
normal A₆ is dihedral of order eight.

The sole extra source premise is π–τ fusion from Held 2.9–2.11; nonfusion,
marking compatibility, transfer, recognition and splitting are discharged here.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Sections 2.9–2.14 and Lemmas 4.1–4.2.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis
open CentralizerStructure CentralizerStructure.FaithfulExclusion

universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
  (D : LocalData G) (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- Held's actual A₆ section, retaining only the earlier π–τ fusion input. -/
public theorem nonempty_alternatingSixSection_of_tau_fusion
    (ht : IsConj D.z (D.a10ModelEmbedding e Coordinates.tau)) :
    Nonempty (AlternatingSixSection
      (Subgroup.centralizer ({D.a10NoncentralInvolution e} : Set G))) := by
  have hf := Fusion.pi_mu_nonfusion D e
  have hl := Fusion.lambda_separation D e
  have hs := exists_s_fusion_of_tau D e hf hl ht
  obtain ⟨d, hd⟩ := exists_xi_isConj_mu_of_separation_and_s_fusion D e
    (xi_separation_of_nonfusion D e hf) hs
  obtain ⟨L⟩ := exists_section213Overgroup_of_xi_fusion D e hf d hd
  obtain ⟨a⟩ := L.alphaRelations hf hd
  obtain ⟨b, ⟨n⟩⟩ := exists_nuSeedRelations_of_tau_fusion D e hf ht
  obtain ⟨F⟩ := nonempty_transferFusion_of_sourceActors D e hf a n
  obtain ⟨M, hM, hindex, hinter⟩ := F.exists_normal_index_four
  let := hM
  obtain ⟨c⟩ := quotientCore_of_transfer_kernel D e F M hindex hinter
  let := c.isPerfect D e hf
  have hbij : Function.Bijective c.derivedMap :=
    ⟨c.derivedMap_injective hf, c.derivedMap_surjective⟩
  apply c.alternatingSixSection_of_derivedMap hbij
  rcases c.model_alternative D e hf with hA | hSeven
  · exact derivedLift_alternating_of_subgroup_alternating c hbij hA
  · obtain ⟨eSeven⟩ := hSeven
    let actors : Actors c := actorsOfRelations c hbij a
      (nuRelationsOfSourceFusion hf a n (crossingFusion_of_seed a n hf))
    let eCore := (extensionCoreEquiv c).trans
      ((MulEquiv.ofBijective c.derivedMap hbij).trans eSeven)
    obtain ⟨x, hx⟩ := exists_order_eight_of_proper_faithful_psl2Seven
      (extensionCore c) eCore (extensionCore_ne_top c hbij.1)
      (extensionCore_centralizer_eq_bot_of_actors actors hf)
    exact (extension_no_order_eight c hf x hx).elim

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis

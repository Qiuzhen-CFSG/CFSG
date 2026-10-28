module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.Assembly
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Action.NaturalImage
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Action.FourCentralizer.Seed
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu.InitialActor
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.Overgroup
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.TauFusionSection

/-!
# Held's corrected six-point geometry from tau fusion

The earlier fusion pi ~ tau constructs the initial nu and alpha actors.
Under the normalized lambda and xi choices their fusions place the three
marked involutions in the supplied A₆. Its faithful conjugation action has
natural symmetric image; the order-four kernel and initial nu actor then
prove that the marked four-group centralizes A₆. The compatible actors and
root-centralization theorem assemble the corrected source six-point data.

Both changes of coordinates fix tau and the original mu. Thus the source
normalization transports tau fusion and the actual supplied alternating
subgroup, without a fusion assumption on every possible marking. The sole
remaining earlier-source premise is pi ~ tau from Held 2.9–2.11.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Sections 2.5, 2.8 and 4.1–5.2, pp.228–236.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
open NoncentralAnalysis NoncentralAnalysis.CentralizerStructure.FaithfulExclusion

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- Construct the supplied section's marked symmetric extension from the
actual earlier source fusion. No actor or action premise remains. -/
public theorem nonempty_markedSection_of_tau_fusion
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj (pi D e) (lam D e))
    (hxi : ¬ IsConj (pi D e) (xi D e))
    (htau : IsConj D.z (D.a10ModelEmbedding e Coordinates.tau))
    (s : AlternatingSixSection
      (centralizer ({D.a10NoncentralInvolution e} : Set G))) :
    Nonempty (MarkedSection D e s) := by
  have hs := exists_s_fusion_of_tau D e hfusion (Fusion.lambda_separation D e) htau
  have hpiLam := pi_lam_fusion_of_source_choice D e hlam
    (by obtain ⟨b, _, _, h⟩ := hs; exact ⟨b, h⟩)
  obtain ⟨d, hd⟩ := exists_xi_isConj_mu_of_separation_and_s_fusion D e
    (xi_separation_of_nonfusion D e hfusion) hs
  obtain ⟨L⟩ := exists_section213Overgroup_of_xi_fusion D e hfusion d hd
  obtain ⟨a⟩ := L.alphaRelations hfusion hd
  have ht := tau_lam_mem_section_of_pi_lam_fusion D e s hfusion hpiLam
  have hx := mu'_xi_mem_section_of_pi_xi_fusion D e s hfusion
    (pi_xi_fusion_of_source_alpha D e hxi d a)
  obtain ⟨⟨es⟩, hc⟩ := section_extension_and_centralizer_card_of_faithful D e s ht hx
    (sectionAction_injective D e s hfusion hpiLam hxi d a)
  obtain ⟨b, ⟨n⟩⟩ := exists_nuSeedRelations_of_tau_fusion D e hfusion htau
  exact ⟨{
    symmetricEquiv := es
    centralizes := section_centralizes_four_of_nuSeed D e s hfusion hpiLam hxi d a hc b n
    pi_mu_mem := pi_mu_mem_section D e s
    tau_lam_mem := ht
    mu'_xi_mem := hx }⟩

/-- Assemble all corrected six-point data at a normalized marking, retaining
exactly the supplied ambient alternating subgroup. -/
public theorem exists_sourceSixLocalData_of_tau_fusion
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj (pi D e) (lam D e))
    (hxi : ¬ IsConj (pi D e) (xi D e))
    (htau : IsConj D.z (D.a10ModelEmbedding e Coordinates.tau))
    (s : AlternatingSixSection
      (centralizer ({D.a10NoncentralInvolution e} : Set G))) :
    ∃ c : Source.SixLocalData D e, c.A = s.ambientSubgroup := by
  obtain ⟨m⟩ := nonempty_markedSection_of_tau_fusion D e hfusion hlam hxi htau s
  obtain ⟨a⟩ := exists_compatibleActors_of_markedSection D e hfusion hlam hxi s m
  exact ⟨sourceSixLocalDataOfMarkedSectionAndActors D e s m a,
    sourceSixLocalDataOfMarkedSectionAndActors_A D e s m a⟩

/-- Normalize the source marking and construct its corrected six-point data.
The original mu and the supplied ambient A₆ are both preserved. -/
public theorem exists_normalized_sourceSixLocalData_of_tau_fusion
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (htau : IsConj D.z (D.a10ModelEmbedding e Coordinates.tau))
    (s : AlternatingSixSection
      (centralizer ({D.a10NoncentralInvolution e} : Set G))) :
    ∃ (e' : D.centralizer ≃* CentralizerModels.a10Centralizer)
      (c : Source.SixLocalData D e'),
      D.a10NoncentralInvolution e' = D.a10NoncentralInvolution e ∧
      c.A = s.ambientSubgroup := by
  have hnorm : ∃ e₀ : D.centralizer ≃* CentralizerModels.a10Centralizer,
      D.a10NoncentralInvolution e₀ = D.a10NoncentralInvolution e ∧
      ¬ IsConj (pi D e₀) (lam D e₀) ∧
      tau D e₀ = tau D e := by
    by_cases hl : IsConj D.z (D.a10ModelEmbedding e Coordinates.lam)
    · refine ⟨Fusion.twistEquiv D e, Fusion.twistEquiv_mu D e, ?_, ?_⟩
      · rw [pi_eq]
        change ¬ IsConj D.z (D.a10ModelEmbedding (Fusion.twistEquiv D e) Coordinates.lam)
        rw [Fusion.twistEquiv_lam]
        exact fun h => Fusion.lambda_separation D e ⟨hl, h⟩
      · change D.a10ModelEmbedding (Fusion.twistEquiv D e) Coordinates.tau =
          D.a10ModelEmbedding e Coordinates.tau
        rw [Fusion.twistEquiv_embedding]
        exact congrArg (D.a10ModelEmbedding e) (Fusion.lambdaTwist_generators 3)
    · refine ⟨e, rfl, ?_, rfl⟩
      rw [pi_eq]
      exact hl
  obtain ⟨e₀, hm₀, hl₀, ht₀⟩ := hnorm
  have hf₀ : ¬ IsConj D.z (D.a10NoncentralInvolution e₀) := by rwa [hm₀]
  obtain ⟨e', s', he', hm, hf, hx, hA⟩ :=
    exists_xi_normalized_section D e₀ hf₀ (transportSection hm₀ s)
  have hl : ¬ IsConj (pi D e') (lam D e') := by
    rcases he' with rfl | rfl
    · exact hl₀
    · simpa only [pi_eq, lam, element_twist D e₀ 6 (by decide)] using hl₀
  have ht' : tau D e' = tau D e := by
    rcases he' with rfl | rfl
    · exact ht₀
    · simpa only [tau, element_twist D e₀ 3 (by decide)] using ht₀
  have ht : IsConj D.z (D.a10ModelEmbedding e' Coordinates.tau) := by
    change IsConj D.z (tau D e')
    rw [ht']
    exact htau
  obtain ⟨c, hc⟩ := exists_sourceSixLocalData_of_tau_fusion D e' hf hl hx ht s'
  exact ⟨e', c, hm.trans hm₀,
    hc.trans (hA.trans (transportSection_ambientSubgroup hm₀ s))⟩

/-- The original tau fusion supplies the section as well as every marked
six-point relation. The chosen centralizer marking preserves the original mu. -/
public theorem exists_sourceSixLocalData_of_original_tau_fusion
    (htau : IsConj D.z (D.a10ModelEmbedding e Coordinates.tau)) :
    ∃ (e' : D.centralizer ≃* CentralizerModels.a10Centralizer)
      (_ : Source.SixLocalData D e'),
      D.a10NoncentralInvolution e' = D.a10NoncentralInvolution e := by
  obtain ⟨s⟩ := nonempty_alternatingSixSection_of_tau_fusion D e htau
  obtain ⟨e', c, hm, _⟩ := exists_normalized_sourceSixLocalData_of_tau_fusion D e
    (Fusion.pi_mu_nonfusion D e) htau s
  exact ⟨e', c, hm⟩

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

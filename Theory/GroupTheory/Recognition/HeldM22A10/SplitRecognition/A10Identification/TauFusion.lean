module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.TauFusionSection
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.TauFusionSix
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SourceAssembly

/-!
# A10 identification from Held's earlier tau fusion

The fusion of the distinguished involution with tau constructs the actual
normal A6 in the noncentral involution centralizer. After choosing the source
lambda and xi markings, the corrected six-point geometry extends to S7 and
supplies all eight Dickson generators. Their image is an actual A10 overgroup
containing the distinguished involution's full centralizer. The two involution
classes and the centralizer order 2880 then exhaust the ambient simple group.

The only additional source input is the fusion from Held 2.9--2.11. No section,
actor, marking, centralizer-order, presentation or overgroup premise remains.
In particular, the older inconsistent six-point interface is not used.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Sections 2.9--2.11 and 4--5.
-/

namespace Theory.GroupTheory.HeldM22A10
open A10Identification A10Identification.NoncentralAnalysis
open A10Identification.OvergroupConstruction
open A10Identification.OvergroupConstruction.LocalGeometry

universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
  (D : LocalData G) (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The entire A10 branch, retaining only the earlier pi--tau fusion. -/
public theorem a10Identification_of_tau_fusion
    (htau : IsConj D.z (D.a10ModelEmbedding e Coordinates.tau)) :
    Nonempty (G ≃* alternatingGroup (Fin 10)) := by
  obtain ⟨s⟩ := nonempty_alternatingSixSection_of_tau_fusion D e htau
  obtain ⟨hf, hc⟩ := D.a10NoncentralAnalysis_of_section e s
  obtain ⟨e', L, hm, _⟩ :=
    SixConstruction.exists_normalized_sourceSixLocalData_of_tau_fusion D e hf htau s
  have hf' : ¬ IsConj D.z (D.a10NoncentralInvolution e') := by rwa [hm]
  have hc' : Nat.card (Subgroup.centralizer
      ({D.a10NoncentralInvolution e'} : Set G)) = 2880 := by rwa [hm]
  obtain ⟨K⟩ := SevenConstruction.exists_sevenLocalData D e' L hf' hc'
  obtain ⟨M, hM, hz⟩ := Source.exists_marked_of_local_geometry D e' L K hc'
  obtain ⟨Q, hQ, ⟨f⟩⟩ := overgroup_of_dicksonRelations D hM hz
  exact a10Identification_of_local_analysis_and_overgroup D e hf hc Q hQ f

end Theory.GroupTheory.HeldM22A10

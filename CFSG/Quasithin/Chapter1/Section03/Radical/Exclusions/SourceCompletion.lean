module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Source.Complete
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.ConcreteSource
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.OutsideSelection.InitialReduction
/-!
# The complete model-exclusion step of1.3.8

For the original radical Configuration, specialize the proved adequate
embedding theorem at p>3. Its retained Held alternative would force p=3,
so the actual nonnormal component has one of the original alternatives.
The full C.2.7 source theorem constructs the pushing-up model. The existing
sieve leaves a binary block, and the proved centerless-factor and guarded
C.1.9 argument contradicts its actual odd trace. Thus X is starred.

No universal legacy Source134, block-commutation or factor-permutation
premise remains. The genuine full C.2.7 theorem remains an earlier input;
the preceding Configuration construction is not asserted by this module.
Source: Aschbacher--Smith, proof of1.3.8, printed pp.513--514.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open XiEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]

theorem Configuration.exists_componentCandidate_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {p : ℕ} {X P L₀ M H₀ : Subgroup G}
    (h : Configuration p T X P L₀ M)
    (hH : H₀ ∈ HOver G (T : Set G))
    (hXH : X ⊔ (T : Subgroup G) ≤ H₀) (hout : ¬ H₀ ≤ M) :
    ∃ K : Subgroup G, ComponentCandidate KnownSimple.IsKnownSimple p T X P M H₀ K := by
  have hTH : (T : Subgroup G) ≤ H₀ := hH.2
  have hsyl : IsSylowIn 2 (T : Subgroup G) H₀ :=
    ⟨T.subtype hTH, by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  have hsqtk := sqtk_of_mem_H hG hH.1
  let : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨S,hS⟩ := h.sylow
  have hinput : LocalInput p T X P H₀ := by
    simpa only [hS] using localInput_of_mem_Xi h.xi hsyl hXH h.odd h.quotient S
  rcases hinput.adequate_knownSimple hsqtk hsyl with hn | ⟨K,hK,hq,hXK,ha⟩
  · exact (hout (h.normalizer_radical ▸
      (normal_subgroupOf_iff_le_normalizer (le_sup_left.trans hXH)).mp hn)).elim
  rcases ha with ha | held
  · exact ⟨K, ⟨hH,hinput,hsyl,hK,hq,hXK,
      surviving_alternatives h.large h.automizer_not_cyclic ha,
      h.pushingUp_setup T hsqtk hXH,
      component_fitting_of_global_He (lemma_1_1_4_6 T (hG.evenCharacteristic T)) hH hK⟩⟩
  · have hp := h.large
    have he := held.1
    omega

theorem Configuration.mem_XiStar_of_C27
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (source : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    {p : ℕ} {X P L₀ M : Subgroup G} (h : Configuration p T X P L₀ M) :
    X ∈ XiStar G (T : Subgroup G) := by
  refine ⟨h.xi,?_⟩
  intro K hK hq hXT
  let hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun (D : Type u) _ _ => ChapterA.Section02.theoremA_knownSimple (G := D))
    (fun (D : Type u) _ _ => ChapterA.Section02.theoremC_knownSimple (G := D))
  have hout := Configuration.initial_not_le_of_A36 hG hA36 h hK hq hXT
  have hH : K ⊔ (T : Subgroup G) ∈ HOver G (T : Set G) :=
    ⟨hK.2.2,fun _ ht => mem_sup_right ht⟩
  obtain ⟨B,hB⟩ := Configuration.exists_componentCandidate_knownSimple hG T h hH hXT hout
  let hc := hB.toPushingUpComponent (ComponentCandidate.not_le_of_configuration h hB)
  have hb := hc.binaryBlockEmbedding h.large (hc.rankOneSieve h.large source)
  exact hb.false_of_centerless_factors T h hH (lemma_1_1_4_6 T (hG.evenCharacteristic T))
end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction

module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.SourceCompletion
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.OddStarModels
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.OddLinearThreeStarModels

/-!
# Starred membership from the original radical configuration

Keep the original outside-component construction. The proved swapped
exclusions eliminate the exchanged rank-one cases; the direct star-catalogue
comparison eliminates the invariant odd linear-three case. Thus the actual
Configuration implies starred membership with no C.2.7 callback.
The configuration's characteristic-normalizer control is still an input.
Source: Aschbacher–Smith, proof of 1.3.8, printed pp.513–514.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open XiEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original 1.3.8 for an actual radical Configuration. The proved source
kernel and star catalogue discharge the invariant branch; the actual
swapped exclusions discharge both rank-one alternatives. -/
theorem Configuration.mem_XiStar_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {p : ℕ} {X P L₀ M : Subgroup G} (h : Configuration p T X P L₀ M) :
    X ∈ XiStar G (T : Subgroup G) := by
  refine ⟨h.xi, ?_⟩
  intro K hK hq hXT
  let hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun (D : Type u) _ _ => ChapterA.Section02.theoremA_knownSimple (G := D))
    (fun (D : Type u) _ _ => ChapterA.Section02.theoremC_knownSimple (G := D))
  have hout := Configuration.initial_not_le_of_A36 hG hA36 h hK hq hXT
  have hH : K ⊔ (T : Subgroup G) ∈ HOver G (T : Set G) :=
    ⟨hK.2.2, fun _ ht => mem_sup_right ht⟩
  obtain ⟨B, hB⟩ := Configuration.exists_componentCandidate_knownSimple hG T h hH hXT hout
  let hc := hB.toPushingUpComponent (ComponentCandidate.not_le_of_configuration h hB)
  rcases hc.alternatives.2 with ⟨hs, hm⟩ | ⟨_, hm⟩
  · exact hc.false_of_swapped T h (lemma_1_1_4_6 T (hG.evenCharacteristic T)) hs hm
  · let _ : Fact p.Prime := ⟨h.prime⟩
    have hp : 5 ≤ p := by
      obtain ⟨k, hk⟩ := h.odd
      have hl := h.large
      omega
    exact not_linearThree_of_source (FullSieve.SourceInterface.input_of_pushingUpComponent hc)
      hp h.odd hm

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction

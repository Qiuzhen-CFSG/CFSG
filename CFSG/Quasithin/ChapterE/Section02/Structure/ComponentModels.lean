module
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentAutomizerSQTK
public import CFSG.Quasithin.ChapterE.Section02.Structure.Alternating.Models
public import CFSG.Quasithin.ChapterA.Section02.Statements
/-!
# Source models for the original generating simple component

Theorem C classifies the actual component. The constructed binary
parabolics and alternating overgroups eliminate those completed source
branches. A nonnormal component is handled in its faithful normalizer
quotient, where its image is normal, simple and core-free and the original
Sylow image remains minimal parabolic. The resulting model equivalences
return through the actual component map to the original K.

The odd-characteristic and sporadic rows are retained for their separate
source geometry; this is the model-selection stage of E.2.2, not the full
final list or its maximal-subgroup conclusions.
Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- The genuine normal simple-component catalogue after the completed binary and alternating reductions. -/
theorem source_normal_simple_models
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup K] (hna : ¬ IsMulCommutative K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    ChapterA.Section02.IsTheoremCOddModel K ∨
    ClassificationModels.IsBenderModel K ∨
    (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL K 3 (2^f)) ∨
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp K 2 (2^f)) ∨
    Nonempty (K ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) ∨
    ChapterA.Section02.IsTheoremCSporadicModel K := by
  have hK := hH.subgroup K
  have hm := hC K inferInstance hna hK.stronglyQuasithin hK.isKGroup
  cases hm with
  | alternating n hn e =>
    rcases Alternating.source_rows T K hna hgen hP ⟨n,hn,e⟩ with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  | odd h => exact Or.inl h
  | bender h => exact Or.inr (Or.inl h)
  | rank_two f hm =>
    rcases BinaryExclusions.rank_two_survivors T K hgen hP hm with h | h | h
    · exact Or.inr (Or.inr (Or.inl ⟨f,h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f,h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.2))))
  | linear_binary n hn hm => exact (BinaryExclusions.not_linear_binary T K hgen hP hn hm).elim
  | sporadic h => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- The same actual source list applies to a nonnormal generating component via its faithful automizer. -/
theorem source_simple_component_models
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) (hK : IsComponent H K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    ChapterA.Section02.IsTheoremCOddModel K ∨
    ClassificationModels.IsBenderModel K ∨
    (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL K 3 (2^f)) ∨
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp K 2 (2^f)) ∨
    Nonempty (K ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) ∨
    ChapterA.Section02.IsTheoremCSporadicModel K := by
  obtain ⟨hA,⟨e⟩,hD,hna,hn,S,hgenD,hPs,_,_⟩ := source_component_as_normal hH T hP hK hgen
  let := hD
  let := hn
  rcases source_normal_simple_models hC hA S hPs (NormalizerAction.componentImage K) hna hgenD with
    h | h | ⟨f,hf,h⟩ | ⟨f,hf,h⟩ | ⟨e'⟩ | h
  · exact Or.inl (h.of_mulEquiv e)
  · exact Or.inr (Or.inl (h.of_mulEquiv e))
  · exact Or.inr (Or.inr (Or.inl ⟨f,hf,h.of_mulEquiv e⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f,hf,h.of_mulEquiv e⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e'.map (fun d => e.trans d))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h.of_mulEquiv e)))))

/-- Construct the genuine simple source component and its reduced family list from the original core-free hypotheses. -/
theorem source_core_free_component_models
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (hJ : ChapterB.minimalParabolicCore T hP = ⊥) :
    ∃ K : Subgroup H, IsComponent H K ∧ IsSimpleGroup K ∧ K ⊔ (T : Subgroup H) = ⊤ ∧
      (ChapterA.Section02.IsTheoremCOddModel K ∨
        ClassificationModels.IsBenderModel K ∨
        (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL K 3 (2^f)) ∨
        (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp K 2 (2^f)) ∨
        Nonempty (K ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) ∨
        ChapterA.Section02.IsTheoremCSporadicModel K) := by
  obtain ⟨K,hK,_,hsi,_,hgen,_⟩ := source_core_free_component hH T hP hs hJ
  let := hsi
  exact ⟨K,hK,hsi,hgen,source_simple_component_models hC hH T hP K hK hgen⟩
end CFSG.Quasithin.ChapterE.Structure

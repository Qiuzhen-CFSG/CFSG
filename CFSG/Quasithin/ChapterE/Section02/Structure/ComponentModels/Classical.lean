module
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels
public import CFSG.Quasithin.ChapterE.Section02.Structure.Sporadic.Source

/-!
# The source simple component has a classical or Bender model

The faithful normalizer quotient makes a generating component a normal
simple supplement of a core-free minimal parabolic. The complete sporadic
exclusion therefore applies also to an exchanged component. Transport back
through the actual component map leaves the odd linear, Bender, binary
linear-three and symplectic rows. No source model is assumed or chosen
independently of the original subgroup.

Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- The original simple component cannot be sporadic, even when the Sylow group exchanges it. -/
theorem source_simple_component_not_sporadic (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) (hK : IsComponent H K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    ¬ ChapterA.Section02.IsTheoremCSporadicModel K := by
  intro hm
  obtain ⟨_,⟨e⟩,hD,hna,hn,S,hgenD,hPs,hcore,_⟩ :=
    source_component_as_normal hH T hP hK hgen
  let := hD
  let := hn
  exact Sporadic.no_model S hPs hcore (NormalizerAction.componentImage K)
    hna hgenD (hm.of_mulEquiv e.symm)

/-- All sporadic, alternating and higher binary rows are removed from the actual source component. -/
theorem source_simple_component_classical_models
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) (hK : IsComponent H K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    ChapterA.Section02.IsTheoremCOddModel K ∨
    ClassificationModels.IsBenderModel K ∨
    (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL K 3 (2^f)) ∨
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp K 2 (2^f)) ∨
    Nonempty (K ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  rcases source_simple_component_models hC hH T hP K hK hgen with
    h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact (source_simple_component_not_sporadic hH T hP K hK hgen h).elim

/-- The same five-family source list is constructed in the original core-free group. -/
theorem source_core_free_component_classical_models
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (hJ : ChapterB.minimalParabolicCore T hP = ⊥) :
    ∃ K : Subgroup H, IsComponent H K ∧ IsSimpleGroup K ∧ K ⊔ (T : Subgroup H) = ⊤ ∧
      (ChapterA.Section02.IsTheoremCOddModel K ∨
        ClassificationModels.IsBenderModel K ∨
        (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL K 3 (2^f)) ∨
        (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp K 2 (2^f)) ∨
        Nonempty (K ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) := by
  obtain ⟨K,hK,_,hsi,_,hgen,_⟩ := source_core_free_component hH T hP hs hJ
  let := hsi
  exact ⟨K,hK,hsi,hgen,source_simple_component_classical_models hC hH T hP K hK hgen⟩
end CFSG.Quasithin.ChapterE.Structure

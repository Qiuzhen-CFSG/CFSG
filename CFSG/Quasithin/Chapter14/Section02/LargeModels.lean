module

public import CFSG.Quasithin.Chapter14.Section02.OutsideParabolic
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.Paired
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.PrimeSharp.Original
public import Theory.GroupTheory.IndexTwoIntersection
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Actual large minimal-parabolic component models

For a nonsolvable original minimal parabolic with generation parameter above one,
the existing E.2 source catalogue and its numerical consumers retain a genuine
marked binary or diagram model on the literal component image. The normal case
uses the full solvable-core upper bound; the exchanged case uses the original
paired clauses, the characteristic-two Bender marking, and the index-two
component normalizer. The odd-prime exchanged row is eliminated by its proved
rank-one bound.

This is the source entry needed before selecting the Bender subgroup K₁ in
14.2.8. It retains the model alternatives instead of asserting a classification
of the resulting weak BN-pair. Source: Aschbacher--Smith E.2.2(1--2),
14.2.7--14.2.8, printed pp.215--216 and 982--984.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE ChapterE.Structure
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

private theorem normal_large_models
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (hn : 1 < generationParameter H) (K : Subgroup H) (hK : K.IsCComponent)
    [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    ∃ f : ℕ, generationParameter H ≤ f ∧ 1 < f ∧
      (BenderModel (ChapterB.minimalParabolicMax T hP) K f ∨
        DiagramModel (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) f) := by
  have hA := ChapterA.Section02.theoremA_knownSimple (G := H)
  have hC := fun (G : Type _) [Group G] [Finite G] =>
    ChapterA.Section02.theoremC_knownSimple (G := G)
  rcases source_normal_geometric_cases hA hC hH T hP hs K hK hgen with h2|h3|hb|hl|hsp|hbi
  · exact (single_odd_linear_false_of_parameter_gt_one hA hH T hP hs K hK hgen h2 hn).elim
  · obtain ⟨p,hp,ho,_,hu|hl⟩ := h3
    · exact (normal_odd_three_false_of_parameter_gt_one hA hH T hP hs K hK hgen hp ho
        (Or.inr hu.2) hn).elim
    · obtain ⟨_,F,hF,hfin,hcard,e,_⟩ := hl
      exact (normal_odd_three_false_of_parameter_gt_one hA hH T hP hs K hK hgen hp ho
        (Or.inl ⟨F,hF,hfin,hcard,⟨e⟩⟩) hn).elim
  · cases hb with
    | linear f hf hm =>
      have hu := normal_classical_parameter_le hA hH T hP hs K hK hgen (.inl ⟨hf,hm⟩)
      exact ⟨f,hu,hn.trans_le hu,Or.inl (Or.inl (source_linear_borel_model T hP hs K hK hgen hf hm))⟩
    | unitary f hf hm =>
      have hu := normal_classical_parameter_le hA hH T hP hs K hK hgen (.inr (.inl ⟨hf,hm⟩))
      exact ⟨f,hu,hn.trans_le hu,Or.inl (Or.inr (source_unitary_borel_model T hP hs K hK hgen hf hm))⟩
    | suzuki m hm he =>
      have hu := (normal_suzuki_generation T hP hs K hK hgen hm he).2
      exact ⟨2*m+1,hu,hn.trans_le hu,Or.inl (Or.inl (source_suzuki_borel_model T hP hs K hK hgen hm he))⟩
  · obtain ⟨f,hf,hm⟩ := hl
    have hu := normal_classical_parameter_le hA hH T hP hs K hK hgen (.inr (.inr ⟨hf,hm⟩))
    exact ⟨f,hu,hn.trans_le hu,Or.inr (source_binary_linear_three_model T hP hs K hK hgen hf hm)⟩
  · obtain ⟨f,hf,hm⟩ := hsp
    have hu := normal_symplectic_parameter_le hA hH T hP hs K hK hgen hf hm
    exact ⟨f,hu,hn.trans_le hu,Or.inr (source_binary_symplectic_model T hP hs K hK hgen hf hm)⟩
  · exact ((Nat.not_le_of_gt hn) (normal_binary_six_parameter_le T hP hs K hK hgen hbi)).elim

theorem source_large_parabolic_models
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hn : 1 < generationParameter H) :
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ (T : Subgroup H) = ⊤ ∧
      ∃ f : ℕ, generationParameter H ≤ f ∧ 1 < f ∧
        ((K.Normal ∧ SingleClauses (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) ∧
          (BenderModel (ChapterB.minimalParabolicMax T hP) K f ∨
            DiagramModel (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) f)) ∨
         (¬K.Normal ∧ ExchangedClauses (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) ∧
          ExchangedModel (ChapterB.minimalParabolicMax T hP) K f ∧
          (normalizer (K : Set H)).index = 2 ∧
          ((normalizer (K : Set H)).subgroupOf (T : Subgroup H)).index = 2)) := by
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
  obtain ⟨K,hK,hqK,hgen,_⟩ := Structure.source_original_component hH T hP hs
  refine ⟨K,hK,hqK,hgen,?_⟩
  by_cases hnorm : K.Normal
  · let := hnorm
    let := hqK
    obtain ⟨f,hu,hf,hm⟩ := normal_large_models hH T hP hs hn K hK hgen
    exact ⟨f,hu,hf,Or.inl ⟨hnorm,source_single_clauses T hP hs K hK hqK hgen,hm⟩⟩
  · rcases source_exchanged_marked_cases ChapterA.Section02.theoremA_knownSimple
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hH T hP hs K hK hgen hnorm with
      ⟨f,hf,hm⟩ | ⟨p,hp,ho,hp7,hm⟩
    · have hc := source_exchanged_clauses (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        hH T hP hs hK hqK hgen hnorm
      have hi : (normalizer (K : Set H)).index = 2 :=
        (Structure.source_original_component_normal_or_index_two ChapterA.Section02.theoremA_knownSimple
          hH T hP hs K hK hgen).resolve_left hnorm
      have hTN : ¬(T : Subgroup H) ≤ normalizer (K : Set H) := by
        intro ht
        have hh : (⊤ : Subgroup H) ≤ normalizer (K : Set H) :=
          hgen ▸ sup_le K.le_normalizer ht
        exact hnorm (normalizer_eq_top_iff.mp (top_unique hh))
      have hu := (Inverted.source_exchanged_intrinsic_escape hH T hP hs K hK hqK hgen hnorm hm).2.1
      exact ⟨f,hu,hf,Or.inr ⟨hnorm,hc,hm,hi,subgroupOf_index_eq_two _ _ hi hTN⟩⟩
    · let : Fact p.Prime := ⟨hp⟩
      exact ((Nat.not_le_of_gt hn) (Structure.NumericalBounds.paired_prime_upper_one
        ChapterA.Section02.theoremA_knownSimple hH T hP hs K hK hgen hnorm hp7 hm)).elim
end CFSG.Quasithin.Chapter14.Section02

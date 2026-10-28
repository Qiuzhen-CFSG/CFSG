module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NormalClauses
public import CFSG.Quasithin.ChapterE.Section02.Structure.OriginalPaired
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The literal exchanged clauses and original E.2.2 structural split

The paired-core and maximal-product theorems discharge both fields of
`ExchangedClauses` on the original carrier. The source component constructor
then chooses K before splitting normality, and supplies either the complete
normal structural clauses or the complete exchanged structural clauses.
The model geometry and generation-parameter equalities remain the separate
inputs required by `FullAlternatives`; neither is assumed by this result.

Source: Aschbacher–Smith E.2.2(1–2), printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- Both original structural fields of the exchanged component alternative. -/
theorem source_exchanged_clauses
    (hA : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremA κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) {K : Subgroup H} (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K)) (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hn : ¬ K.Normal) :
    ExchangedClauses (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) :=
  ⟨Structure.PairedCore.source hA hH T hP hs hK hqK hgen hn,
    Structure.source_original_exchanged_product hA hH T hP hs hK hqK hgen hn⟩

/-- The genuine original component and complete structural split, before the remaining model geometry. -/
theorem source_component_structural_cases
    (hA : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremA κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) :
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      (⊤ : Subgroup H) = K ⊔ (T : Subgroup H) ∧
      IsSQTK κ (H ⧸ sourceKernel (ChapterB.minimalParabolicMax T hP)) ∧
      ((K.Normal ∧ SingleClauses (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H)) ∨
       (¬ K.Normal ∧ ExchangedClauses (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H))) := by
  obtain ⟨K,hK,hqK,hgen,_⟩ := Structure.source_original_component hH T hP hs
  refine ⟨K,hK,hqK,hgen.symm,Structure.source_star_sqtk (hA H) hH T hP hs,?_⟩
  by_cases hn : K.Normal
  · let := hn
    exact Or.inl ⟨hn,source_single_clauses T hP hs K hK hqK hgen⟩
  · exact Or.inr ⟨hn,source_exchanged_clauses hA hH T hP hs hK hqK hgen hn⟩
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

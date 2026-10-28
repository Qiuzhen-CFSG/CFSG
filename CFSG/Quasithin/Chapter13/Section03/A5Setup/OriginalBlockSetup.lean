module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceBaumannBlocks

/-!
# The original A₅ block alternative under Hypothesis 13.3.1

The genuine original hypothesis constructs its Fundamental Setup without
normalization. The local Thompson and E.2.3 arguments then give either
Baumann normalizer control or an alternating-five block on the original L.
The block's subnormality is asserted inside the actual local join L₀T;
the module marking is also retained intrinsically on L.

This is the source reduction at the start of the A₅ case in 10.2.1,
applied at the original 13.3.1 normalization consumer. The remaining
block geometry and centralizer argument are not assumed or asserted.
Source: Aschbacher–Smith, 10.2.1 and 13.3.2(2), printed pp.742–743,884–885.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The Baumann exception is reduced to the actual original A₅ block,
with no chosen-module or full/local-module equality premise. -/
theorem baumann_normalizer_le_or_original_alternating_block
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
        normalizer (localOrbit T L : Set G) ∨
      (ChapterC.IsBlock (L.subgroupOf (localJoin T L)) ∧
        ChapterC.IsAlternatingBlock (L.subgroupOf (localJoin T L)) 5 ∧
        ChapterC.IsAlternatingBlock L 5) := by
  classical
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  by_cases hout : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal
  · exact Or.inl hout
  · exact Or.inr (Chapter10.source_a5_original_block_of_baumann_not_controlled D e hn hout)

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality

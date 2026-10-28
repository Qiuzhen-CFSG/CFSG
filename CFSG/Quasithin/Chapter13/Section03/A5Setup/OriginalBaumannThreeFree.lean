module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5BaumannThreeFree

/-!
# The original Hypothesis 13.3.1 Baumann normalizer is three-free

The literal A₅ branch supplies its original Fundamental Setup. The paired
Baumann action and cubic-residual theorem give the normalizer exclusion in
10.2.1 without assuming normalization of the original component.

Source: Aschbacher–Smith, 10.2.1 and 13.3.2(2), pp.743 and 884–885.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The normalizer inside the original M has no cubic factor. -/
theorem maximal_baumann_normalizer_three_free
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G)) :
    Nat.Coprime 3 (Nat.card
      (normalizer (localOrbit T L : Set G) ⊓
        normalizer (ChapterB.baumann (T : Subgroup G) : Set G) : Subgroup G)) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact Chapter10.source_a5_maximal_baumann_normalizer_three_free D e hn hout

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality

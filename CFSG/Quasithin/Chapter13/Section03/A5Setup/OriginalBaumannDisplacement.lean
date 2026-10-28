module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5BaumannDisplacement

/-!
# Actual 13.3.1 paired-five displacement on the Baumann center

Construct the original Fundamental Setup and apply the original A5 source
theorem. The two marked residual factors and their displacement lines use
its literal local module and centralizer quotient throughout.

Source: Aschbacher–Smith 10.2.1 and 13.3.2(2), pp.743 and884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem baumann_center_displacement
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      Chapter10.SourcePairedBaumannDisplacement D := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact ⟨D,Chapter10.source_a5_baumann_center_displacement D e hn hout⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality

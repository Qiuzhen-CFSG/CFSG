module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalFixedCenterTransvection
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterRankOne

/-!
# The original 13.3.1 fixed-center quotient involution

The original Fundamental Setup supplies its literal reduced H-star orbit
and faithful centralizer-quotient action, including a nonidentity involution
with displacement dimension exactly one. Generation of the whole orbit
module by that displacement remains a separate source obligation.

Source: Aschbacher–Smith 10.2.1, G.6.4 and13.3.2(2), pp.743,345–346,884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem exists_original_fixed_center_rank_one
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L, Chapter10.SourceFixedCenterRankOne D := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact ⟨D,Chapter10.source_exists_fixed_center_rank_one D e hn hne hout⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality

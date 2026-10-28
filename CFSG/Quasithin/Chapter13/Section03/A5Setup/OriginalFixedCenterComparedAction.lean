module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterComparedAction
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalFixedCenterTransvection
/-!
# Original 13.3.1 consumer for the fixed-center model comparison

The literal Hypothesis 13.3.1 setup supplies the same D, quotient, original
commutator module and model comparison as the Chapter 10 theorem. This keeps
all ambient exclusions explicit while exposing the exact source contract to
Section 03 assembly.
Source: Aschbacher--Smith 10.2.1 and13.3.2(2), printed pp.743,884--885.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem exists_original_fixed_center_compared_action
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      Chapter10.SourceFixedCenterComparedAction D := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact ⟨D,Chapter10.source_exists_fixed_center_compared_action D e hn hne hout⟩
end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality

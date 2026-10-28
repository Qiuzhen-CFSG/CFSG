module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterBinaryPlanes
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalFixedCenterTransvection

/-!
# The original 13.3.1 fixed-center action has two binary planes

The original fundamental setup supplies the Chapter 10 action, with the same
commutator module and centralizer quotient. The three-free maximal subgroup
excludes the paired natural-five row, leaving the paired binary-plane action
of dimension four. The subsequent containing-component argument remains a
separate source obligation.

Source: Aschbacher–Smith, 10.2.1 and 13.3.2(2), printed pp.743,884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem exists_original_fixed_center_binary_plane_action
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      Chapter10.SourceFixedCenterBinaryPlaneAction D := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact ⟨D,Chapter10.source_exists_fixed_center_binary_plane_action D e hn hne hout⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality

module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5MinimalParabolic

/-!
# The original A₅ input to Chapter 10

The uniform A₅ clause of Hypothesis 13.3.1 gives maximality of the original
faithful component and hence the original Fundamental Setup. If the component
is not normalized by the Sylow subgroup, its actual local join is a minimal
parabolic. Consequently the common-normal theorem controls every nonzero
invariant two-subgroup which is Sylow over the orbit component. On this same
setup, E.2.3 supplies the Baumann normalizer bound or its marked symmetric-five
exception once the earlier full/local-module equality is supplied.

This discharges the minimal-parabolic premise of the original 10.2.1 argument
at the literal 13.3.1 consumer, without choosing a normalized-component module.
Source: Aschbacher–Smith, 10.1.2(6), 10.2.1, and 13.3.2(2),
printed pp.742–743 and 884–885.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original nonnormal A₅ branch supplies its own minimal parabolic and
common-normal control before the module classification and five-action case. -/
theorem exists_original_parabolic_setup
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      ChapterB.IsMinimalParabolicOver
        (T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)) ⊤ ∧
      (∀ R : Subgroup G, R ≠ ⊥ → R ≤ (T : Subgroup G) →
        (T : Subgroup G) ≤ normalizer (R : Set G) →
        Chapter1.IsSylowIn 2 R (localOrbit T L ⊔ R) →
        normalizer (R : Set G) ≤ D.maximalLocal) ∧
      (D.fullModule = D.moduleSubgroup →
        normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal ∨
          Chapter10.SourceFiveAction D) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact ⟨D, Chapter10.source_a5_minimal_parabolic D e hn,
    Chapter10.source_a5_normalizer_le_of_orbit_sylow D e hn,
    Chapter10.source_a5_baumann_normalizer_or_five_action D e hn⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality

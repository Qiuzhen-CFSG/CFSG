module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceParabolicAction

/-!
# The actual Chapter 12 input to the Chapter 10 parabolic branch

Hypothesis 12.2.1 constructs the original FSU before normalization of L.
Its local two-residual is L₀. The common-normal theorem controls every
T-invariant two-subgroup which is Sylow in its product with L₀. In the
original minimal-parabolic rows, the complete E.2.3 source supplies either
Baumann normalizer control or the actual marked symmetric-five exception.

The earlier marked-module analysis retains precisely the minimal-parabolic
and full/local-module equality premises; the symmetric-five elimination
also remains separate. No chosen module for L or normalization is assumed.
Source: Aschbacher–Smith, 10.1.2–10.2.1, pp.742–743, applied in12.2.2,
pp.794–795.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The complete normalizer-control reduction on a single actual original
FSU selected from the Chapter 12 hypothesis. -/
theorem Hypothesis1221.exists_original_parabolic_control
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      ((pResidual 2 (localJoin T L)).map (localJoin T L).subtype = localOrbit T L) ∧
      (Order.HasUniqueMaximalOver (T : Subgroup G) (localJoin T L) →
        ∀ R : Subgroup G, R ≠ ⊥ → R ≤ (T : Subgroup G) →
          (T : Subgroup G) ≤ normalizer (R : Set G) →
          Chapter1.IsSylowIn 2 R (localOrbit T L ⊔ R) →
          normalizer (R : Set G) ≤ D.maximalLocal) ∧
      (ChapterB.IsMinimalParabolicOver
          (T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)) ⊤ →
        D.fullModule = D.moduleSubgroup →
        normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal ∨
          Chapter10.SourceFiveAction D) := by
  obtain ⟨D⟩ := h.exists_original_fundamentalSetup
  exact ⟨D, Chapter10.source_join_residual D,
    Chapter10.source_normalizer_le_of_orbit_sylow D,
    Chapter10.source_baumann_normalizer_or_five_action D⟩

end CFSG.Quasithin.Chapter12.Section02

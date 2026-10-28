module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.Terminal.Complete
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.DiagonalCore.FullAction

/-!
# Diagonal-core control in the small-offender argument

The earlier natural pair supplies the completed local seed and full-action
proofs, so V lies in the two-core of the actual diagonal centralizer without
a weak-closure equality. Constructing that pair from the literal geometry
proves `DiagonalCoreAt` and discharges it in the terminal TI contradiction.

The small-offender consumer retains recognition and earlier half-Sylow
uniqueness; their discharge and final assembly remain with
`qt-d-10-nona5-small-offender`. No claim of the full small-offender theorem
is made here.
Source: Aschbacher--Smith 10.2.11--12, printed pp.753--755.
-/

public noncomputable section
-- Adapted from Geometry/CoreReduced/Source.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G]

/-- The exact original centralizer-core and full-action reducedness contract. -/
theorem coreReducedAt (T : Sylow 2 G) : CoreReducedAt T :=
  coreReduced_of_source_inputs (Seed.seedAnalysisAt T)
    (FullAction.Natural.fullActionCentralizationAt T)

/-- All three clauses of 10.2.11 on the original diagonal configuration. -/
theorem centralizer_twoCore_reduced {T : Sylow 2 G} {L : Subgroup G}
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    {s : SourceLinearThreePair T D} {a b : G} (c : Configuration s a b) :
    centralizerModule a b ≤ centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2) ∧
    centralizer ({a*b} : Set G) ⊓ centralizer (centralizerModule a b : Set G) ≤
      D.maximalLocal ⊓ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) ∧
    (centralizerSeed T L (a*b) < componentSpan T L (a*b) →
      IsPReduced 2 ((centralizerModule a b).subgroupOf (centralizer ({a*b} : Set G)))) ∧
    D.fullModule ≤ (centralizer ({a*b} : Set G)).pCoreIn 2 := by
  have hseed := Seed.seedAnalysisAt T L D s a b c
  obtain ⟨hcore, hred⟩ := coreReducedAt T c.many L D s c.fixed c.ti a b
    c.first_mem c.second_mem c.first_ne c.second_ne c.first_fixed c.second_fixed
    c.central c.order
  exact ⟨c.span_central_core_of_seedJoin_core hseed.core_bound,
    c.kernel_le_moved_normalizer, hred, hcore⟩


end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced

namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Subgroup Theory.GroupTheory Chapter3.Section02 ChapterE
open SourceLinearThreeReplacement.Earlier
variable {G : Type*} [Group G] [Finite G]

/-- The original 10.2.11 core conclusion precedes every weak-closure equality. -/
theorem diagonalCoreAt (T : Sylow 2 G) : DiagonalCoreAt T := by
  intro hmany L D m hn hpoint hz hti t ht htn a b ha hb hane hbne haf hbf hc ho
  let s : SourceLinearThreePair T D :=
    { exchange := t
      exchange_mem := ht
      exchange_moves := htn
      full_eq_local := m.full_eq_local
      generated := source_nonnormal_fullModule_eq_moved_pair D hn ht (m.crossed t ht htn)
      crossed := m.crossed t ht htn
      quotient := m.quotient
      natural := m.natural
      pointCentralizers := hpoint }
  have hti' : ∀ x : G, ⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom = ⊥ ∨
      (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom = ⁅D.fullModule,L⁆ := by
    intro x
    by_cases hx : x ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)
    · exact Or.inr (mem_normalizer_iff_map_conj_eq.mp hx)
    · exact Or.inl (bot_unique (hti x hx))
  exact (Geometry.CoreReduced.coreReducedAt T hmany L D s hz hti'
    a b ha hb hane hbne haf hbf hc ho).1

/-- The terminal natural contradiction now retains only the earlier component-normalizer input. -/
theorem naturalSmallCorankExclusion_of_halfSylow
    {T : Sylow 2 G} (hhalf : PointControl.HalfSylowUniqueAt T) :
    NaturalSmallCorankExclusionAt T :=
  naturalSmallCorankExclusion_of_halfSylow_core hhalf (diagonalCoreAt T)

/-- Actual original small-offender consumer with the diagonal-core and terminal branches discharged. -/
theorem nonnormalSmallOffender_of_recognition_halfSylow
    {T : Sylow 2 G} (hrecognition : RecognitionAt T)
    (hhalf : PointControl.HalfSylowUniqueAt T) : SourceNonnormalSmallOffenderAt T :=
  source_nonnormalSmallOffender_of_source_steps hrecognition
    (naturalSmallCorankExclusion_of_halfSylow hhalf)

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank

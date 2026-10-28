module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Assembly
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction.Natural.Source

/-!
# The centralizer two-core and reducedness theorem

The original local residual action bounds O₂(XT) and proves reducedness of
V_z for the entire faithful G_z action. The natural point-centralizer action
supplies the fixed line for the corrected transvection contradiction.
Together with the normal-seed branch, this puts V in O₂(G_z).

All local seed and natural-action premises are discharged here. The geometry
consumer retains only the independent fixed-space/TI and escape assertions,
whose final assembly belongs to `qt-d-10-replacement-centralizer-geometry`.
Source: Aschbacher--Smith 10.2.11, printed pp.753--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G]

/-- The exact original centralizer-core and full-action reducedness contract. -/
theorem coreReducedAt (T : Sylow 2 G) : CoreReducedAt T :=
  coreReduced_of_source_inputs (Seed.seedAnalysisAt T)
    (FullAction.Natural.fullActionCentralizationAt T)

/-- All three clauses of 10.2.11 on the original diagonal configuration. -/
theorem centralizer_twoCore_reduced {T : Sylow 2 G} {L : Subgroup G}
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    {s : SourceLinearThreeSurvivor T D} {a b : G} (c : Configuration s a b) :
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

/-- Apply the completed core theorem to the literal centralizer geometry.
The fixed-space/TI and escape proofs remain with the geometry assembly owner. -/
theorem centralizerGeometry_of_fixedSpaceTI_escape {T : Sylow 2 G}
    (hfixed : FixedSpaceTIAt T) (hescape : EscapeAt T) : CentralizerGeometryAt T :=
  centralizerGeometry_of_source_inputs hfixed (coreReducedAt T) hescape

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced

module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Reduced
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Assembly

/-!
# Assembly of the diagonal-centralizer two-core argument

The local seed calculation supplies central-core control and the full-action
reducedness theorem. If X is normal, its action generates V modulo E, so V
centralizes V_z. Otherwise the independent full-action argument supplies the
same centralization. Relative normality in C_Gz(V_z) then puts V in O₂(G_z).

The two remaining source inputs are explicit and are not asserted here.
This conditional assembly feeds the actual geometry and replacement consumers.
Source: Aschbacher--Smith 10.2.11, printed pp.753--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Discharge exactly the CoreReducedAt contract from its two source branches. -/
theorem coreReduced_of_source_inputs
    (hseed : SeedAnalysisAt T) (haction : FullActionCentralizationAt T) : CoreReducedAt T := by
  intro hmany L D s hfixed hti a b ha hb hane hbne haf hbf hz ho
  let c : Configuration s a b := ⟨hmany,hfixed,hti,ha,hb,hane,hbne,haf,hbf,hz,ho⟩
  have h := hseed L D s a b c
  have hcentral := c.span_central_core_of_seedJoin_core h.core_bound
  have hr := c.reduced_of_seedAnalysis h
  refine ⟨c.full_core_of_centralizes ?_, hr⟩
  by_cases he : centralizerSeed T L (a*b) = componentSpan T L (a*b)
  · have hn : centralizer ({a*b} : Set G) ≤
        normalizer (centralizerSeed T L (a*b) : Set G) := by
      rw [he]
      exact le_normalizer_conjugateSpanBy _ _
    exact c.full_centralizes_of_seed_normalizes h hn
  · have hlt : centralizerSeed T L (a*b) < componentSpan T L (a*b) :=
      lt_of_le_of_ne (le_conjugateSpanBy _ _) he
    exact haction L D s a b c h hcentral hlt (hr hlt)

/-- The actual centralizer-geometry consumer, preserving the independent
fixed-space/TI and escape producers owned by the parent geometry assembly. -/
theorem centralizerGeometry_of_core_source_inputs
    (hfixed : FixedSpaceTIAt T) (hescape : EscapeAt T)
    (hseed : SeedAnalysisAt T) (haction : FullActionCentralizationAt T) :
    CentralizerGeometryAt T :=
  centralizerGeometry_of_source_inputs hfixed
    (coreReduced_of_source_inputs hseed haction) hescape

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced

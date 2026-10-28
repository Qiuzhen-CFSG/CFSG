module

public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveQuotientCentralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveActorCorrection
public import Theory.GroupTheory.PResidual.NormalizedSupplement

/-!
# Lifting a two-perfect actor through an A₅ block's two-core

Fixation of L/O₂(L) implies fixation of the genuine natural module U(L).
The C.1.13 cohomology calculation then corrects every actor by an element
of U(L) to centralize L. Since U(L) is a two-group, two-perfection absorbs
this supplement. In particular no central two-cover is discarded.

This is the lifting step in Aschbacher--Smith 15.1.21(ii), printed p.1098.
The quotient-action calculation is a separate premise, not proved here.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G]

/-- A two-perfect actor fixing the full module layer centralizes the whole A₅ block. -/
theorem IsAlternatingBlock.twoPerfect_centralizes_of_blockU_centralizes
    {L Y : Subgroup G} (hL : IsAlternatingBlock L 5) (hY : IsPPerfect 2 Y)
    (hn : Y ≤ normalizer (L : Set G))
    (hfix : Y ≤ centralizer ((blockU L).map L.subtype : Set G)) :
    Y ≤ centralizer (L : Set G) := by
  let U := (blockU L).map L.subtype
  let C := centralizer (L : Set G)
  have hLC : L ≤ centralizer (C : Set G) := le_centralizer_iff.mpr le_rfl
  have hUC : U ≤ normalizer (C : Set G) :=
    (map_subtype_le _).trans (hLC.trans (centralizer_le_normalizer _))
  have hcover : Y ≤ C ⊔ U := by
    intro y hy
    obtain ⟨u, hu⟩ := hL.exists_centralizing_correction y (hn hy) (hfix hy)
    have huU : ((u : L) : G) ∈ U := mem_map_of_mem L.subtype u.property
    have hh := (C ⊔ U).mul_mem
      ((show U ≤ C ⊔ U from le_sup_right) (U.inv_mem huU))
      ((show C ≤ C ⊔ U from le_sup_left) hu)
    simpa only [inv_mul_cancel_left] using hh
  exact le_of_isPPerfect_of_le_sup_of_normalizes Y C U hY
    ((pCore_isPGroup.to_le blockU_le_core).map L.subtype) hUC hcover

/-- Fixation of the literal core quotient lifts across all central two-covers. -/
theorem IsAlternatingBlock.twoPerfect_centralizes_of_quotient_centralizes
    {L Y : Subgroup G} (hL : IsAlternatingBlock L 5) (hY : IsPPerfect 2 Y)
    (hn : Y ≤ normalizer (L : Set G)) (hc : ⁅Y,L⁆ ≤ L.pCoreIn 2) :
    Y ≤ centralizer (L : Set G) :=
  hL.twoPerfect_centralizes_of_blockU_centralizes hY hn
    (hL.quotient_centralizer_le_blockU_centralizer hn hc)

end CFSG.Quasithin.ChapterC

module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityShortCentralizer.Marked
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityThompson

/-!+# Discharging the short-root inputs to the prepared triality exit

The designated native Sylow centralizer and the full marked ambient
centralizer supply both inputs to the published Thompson comparison.
Its existing recognition application then gives the literal Chapter 12
global exit. The supplied reversed comparison and its constructed extension
are unchanged, and no centralizer or order premise remains.

Source: Aschbacher--Smith F.4.40--44, printed pp.294--296, and 5.3.3--4,
printed p.659 (`refs/quasithin.pdf`). Selection of the prepared comparison
from an arbitrary residual is a separate classification obligation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original prepared triality row, with both short-root inputs proved. -/
theorem rankOne_globalExit_of_triality_short_centralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    RankOneModule.GlobalExit G := by
  apply D.rankOne_globalExit_of_triality_prepared_short_centralizer
    h hmany hn hpsl hH d hp m hm e
  · exact Triality.Standard.ShortRootCentralizer.centralizer_sylow m hm
      (d.triality_local_structure (D.rankOne_generic_input_of_many h hmany hn hpsl)
        hH.1.1.2 hp m hm e).2.1 1 one_ne_zero
  · exact D.rankOne_global_triality_short_centralizer_full_marked
      h hmany hn hpsl hH d hp m hm e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

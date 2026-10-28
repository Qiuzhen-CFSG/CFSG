module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Common
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityShortCentralizer.Extension

/-!
# The marked triality pair stabilizer in Chapter 12

The original chosen-module input places the common centralizer of the
supplied short and long roots in the original whole-normalizer overlap.
The same comparison and constructed extension are retained throughout.

Source: Aschbacher--Smith F.4.42, printed pp.294--295, and 5.3.3, p.659
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual chosen-module application to the original marked pair. -/
theorem rankOne_global_triality_short_long_common_centralizer
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
    let P := binaryParameters m hm
    let t : G := (e.right.symm (Global.TrialityCompletionFusion.shortElement P rfl)).val
    let z : G := (e.right.symm (Global.TrialityCompletionFusion.longElement P rfl)).val
    centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
  d.triality_short_long_common_centralizer
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

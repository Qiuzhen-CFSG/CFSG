module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Action
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The prepared triality plane and automizer in Chapter 12

The chosen-module input supplies the original prepared context, including
m = n > 1. The original comparison marks the central radical plane and
both pinned roots, and the nonsolvable action reduces F.4.42 to the one
remaining fixed-coset premise in the actual short-root centralizer.

Source: Aschbacher–Smith F.4.42, p.295, and 5.3.3, p.659
(`refs/quasithin.pdf`). This conditional reduction does not assert F.4.42.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The characteristic plane and the I.8.5 reduction for the given comparison. -/
theorem rankOne_global_triality_short_centralizer_of_long_unique_fixed
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
    let f := (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0).subtype.comp
      e.left.symm.toMonoidHom
    let v : G := f (TrialityShortAction.short P rfl)
    v = (e.right.symm (TrialityCompletionFusion.shortElement P rfl)).val ∧
      (TrialityShortAction.longMark rfl f).val =
        (e.right.symm (TrialityCompletionFusion.longElement P rfl)).val ∧
      TrialityShortAction.plane f = (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ∧
      ((∃! q : centralizer ({v} : Set G) ⧸ (normalizer (L : Set G)).subgroupOf
          (centralizer ({v} : Set G)), TrialityShortAction.longMark rfl f • q=q) →
      centralizer ({v} : Set G) ≤ normalizer (L : Set G)) :=
  d.triality_short_centralizer_of_long_unique_fixed
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

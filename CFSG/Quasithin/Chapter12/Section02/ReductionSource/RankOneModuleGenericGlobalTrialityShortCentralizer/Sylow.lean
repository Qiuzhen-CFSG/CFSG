module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Sylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The actual short-root Sylow centralizer in the Chapter 12 triality row

The native full-centralizer and Levi-projection results discharge F.4.40's
model extremality premise for the literal chosen-module comparison. The
whole-Borel marking also identifies the original right marker with its
central-parabolic left transport. These results retain q = 4. Full ambient
centralizer containment, the remaining F.4.42 obligation, is separate.

Source: Aschbacher–Smith F.4.27(4)(ii), F.4.40, F.4.42, printed pp.288,
294–295, and the application 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates.LeviCommutators
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- F.4.40 for the actual short root, with its native Sylow premise proved. -/
theorem rankOne_global_triality_short_centralizer_sylow
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
    ∃ R : Sylow 2 (centralizer ({t} : Set G)),
      (R : Subgroup _) = (T : Subgroup G).subgroupOf (centralizer ({t} : Set G)) :=
  d.triality_short_centralizer_sylow (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m hm e

/-- The same short root lies in the central radical and has identical left
and right transports under the supplied comparison. -/
theorem rankOne_global_triality_short_marker_left
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
    ∃ v : parabolic P .central,
      v.val = short P rfl 2 1 ∧ v.val ∈ radical P .central ∧
      (e.right.symm (Global.TrialityCompletionFusion.shortElement P rfl)).val =
        (e.left.symm v).val ∧
      (e.right.symm (Global.TrialityCompletionFusion.shortElement P rfl)).val ∈
        normalizer (L : Set G) :=
  d.triality_short_marker_left (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m hm e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

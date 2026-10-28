module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Containment
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The original Chapter 12 triality short-root centralizer bound

The chosen-module hypotheses supply the original rank-one input. The
prepared F.4.42 theorem then puts the full ambient centralizer of the given
short-root marker in N_G(L). The same reversed comparison is retained;
there is no model-Sylow, fixed-coset or ambient-order premise.

Source: Aschbacher--Smith F.4.42, printed p.295, applied in 5.3.3,
printed p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- F.4.42 for the literal chosen-module triality row. -/
theorem rankOne_global_triality_short_centralizer_le_normalizer
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
    centralizer
      ({(e.right.symm (TrialityCompletionFusion.shortElement
        (binaryParameters m hm) rfl)).val} : Set G) ≤ normalizer (L : Set G) :=
  d.triality_short_centralizer_le_normalizer
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

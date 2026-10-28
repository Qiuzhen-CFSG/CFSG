module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Marked
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityShortCentralizer.Containment

/-!
# The full marked short-root centralizer in Chapter 12

The chosen-module preparation constructs its original whole-normalizer
marking internally. Restriction gives the entire ambient short centralizer
and its pinned root in the very same extension. This is the literal
short-side input for the later F.4.43 comparison, with no order premise.

Source: Aschbacher--Smith F.4.42--43, printed pp.295--296, and 5.3.3,
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

/-- The original whole-normalizer marking on the entire ambient centralizer. -/
theorem rankOne_global_triality_short_centralizer_full_marked
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
    let a := d.trialityNormalizerMarking
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm e
    let t := (e.right.symm (TrialityCompletionFusion.shortElement P rfl)).val
    ∃ ht : centralizer ({t} : Set G) ≤ normalizer (L : Set G),
      ∃ k : centralizer ({t} : Set G) ≃* centralizer
          ({a.extension.baseHom (TrialityCompletionFusion.shortElement P rfl).val} :
            Set a.extension.carrier),
        (∀ x, (k x).val = inclusion a.extension.right_le
          (a.comparison.left (inclusion ht x))) ∧
        k ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ =
          ⟨a.extension.baseHom (TrialityCompletionFusion.shortElement P rfl).val,
            mem_centralizer_singleton_iff.mpr rfl⟩ :=
  d.triality_short_centralizer_full_marked
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm e
    (d.trialityNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl)
      hH hp m hm e)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityLongCentralizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityExtensionOrder

/-!
# Full long-root centralizers for the original chosen-module triality row

The full ambient centralizer is identified with the full centralizer in the
published constructed extension for the given comparison. The isomorphism
retains the original right full-normalizer map and the pinned involution.
This supplies the long-root datum for F.4.43; short-root containment and the
ambient order bound remain to be proved before prepared recognition applies.

Source: Aschbacher--Smith F.4.43 and 5.3.3, printed pp.296 and659
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.SourceCompletion.TrialityNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal source long-root centralizer is isomorphic to the full
centralizer in the same constructed extension, with its original marking. -/
theorem rankOne_global_triality_long_centralizer_full_marked
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (nativeAmalgam m hm).reverse) :
    let a := d.trialityNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl)
      hH hp m hm e
    let P := binaryParameters m hm
    let z := (e.right.symm (Global.TrialityCompletionFusion.longElement P rfl)).val
    ∃ hz : centralizer ({z} : Set G) ≤ normalizer (residual H : Set G),
      ∃ k : centralizer ({z} : Set G) ≃* centralizer
          ({a.extension.baseHom (Global.TrialityCompletionFusion.longElement P rfl).val} :
            Set a.extension.carrier),
        (∀ x, (k x).val = inclusion a.extension.left_le
          (a.comparison.right (inclusion hz x))) ∧
        k ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩ =
          ⟨a.extension.baseHom (Global.TrialityCompletionFusion.longElement P rfl).val,
            mem_centralizer_singleton_iff.mpr rfl⟩ :=
  d.triality_long_centralizer_full_marked (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m hm e _

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Extension
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityShortCentralizer.Sylow

/-!
# The Chapter 12 short-root centralizer in the same triality extension

The literal whole-normalizer comparison maps the local short-root centralizer
onto the full centralizer in the constructed extension. The fixed-tree proof
controls the entire extension, including its outer automorphisms, and the
root equation retains the original reversed comparison. The ambient equality
with this local centralizer is the remaining F.4.42 obligation.

Source: Aschbacher–Smith F.4.27(4)(ii), F.4.42, printed pp.288 and 295,
with the application 5.3.3, p.659 (`refs/quasithin.pdf`).
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

/-- The literal short-root equation under the original whole-normalizer map. -/
theorem rankOne_global_triality_short_extension_marker
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
    let M := d.trialityNormalizerMarking
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm e
    let t : G := (e.right.symm (Global.TrialityCompletionFusion.shortElement P rfl)).val
    ∃ ht : t ∈ normalizer (L : Set G),
      (M.comparison.left ⟨t,ht⟩).val = MulAut.conj (short P rfl 2 1) :=
  d.triality_short_extension_marker (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m hm e

/-- The original local centralizer corresponds to the whole extension
centralizer, without a model-centralizer or outer-automorphism premise. -/
theorem rankOne_global_triality_short_extension_centralizer_image
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
    let M := d.trialityNormalizerMarking
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm e
    let t : G := (e.right.symm (Global.TrialityCompletionFusion.shortElement P rfl)).val
    let f := (inclusion M.extension.right_le).comp M.comparison.left.toMonoidHom
    ((centralizer ({t} : Set G)).subgroupOf (normalizer (L : Set G))).map f =
      centralizer ({M.extension.baseHom (short P rfl 2 1)} : Set M.extension.carrier) :=
  d.triality_short_extension_centralizer_image
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

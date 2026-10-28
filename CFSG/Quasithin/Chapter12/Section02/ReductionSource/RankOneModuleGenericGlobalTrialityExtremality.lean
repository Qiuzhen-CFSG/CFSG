module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtremality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityShortSylow

/-!
# Triality F.4.40 for the literal Chapter 12 pair

The same supplied comparison retains its two distinct ambient root classes.
An involution extremal in the genuine model's common Sylow is then extremal
in the original ambient Sylow. The statement retains exactly F.4.40's model
Sylow-centralizer premise. It does not assert full short-root centralizer
containment or completion recognition.

Source: Aschbacher--Smith F.4.35 and F.4.40, printed pp.292 and 294,
and 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The exact supplied comparison keeps the two marked roots nonconjugate. -/
theorem rankOne_global_triality_comparison_involution_nonfusion
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
    ¬ IsConj (e.right.symm (Global.TrialityCompletionFusion.longElement P rfl)).val
      (e.right.symm (Global.TrialityCompletionFusion.shortElement P rfl)).val :=
  d.triality_comparison_involution_nonfusion (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m hm e

/-- Conjugacy through the supplied maps reflects to the genuine model. -/
theorem rankOne_global_triality_comparison_fusion_reflects
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (x y : parabolic (binaryParameters m hm) .arms)
    (hx : x.val ∈ unipotent (binaryParameters m hm))
    (hy : y.val ∈ unipotent (binaryParameters m hm))
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2)
    (hxy : IsConj (e.right.symm x).val (e.right.symm y).val) :
    IsConj x.val y.val :=
  d.triality_comparison_fusion_reflects (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m hm e x y hx hy hx2 hy2 hxy

/-- An involution extremal in the model stays extremal in the original group. -/
theorem rankOne_global_triality_involution_centralizer_sylow
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (v : parabolic (binaryParameters m hm) .arms)
    (hv : v.val ∈ unipotent (binaryParameters m hm)) (hv2 : orderOf v = 2)
    (hmodel : ∃ R : Sylow 2 (centralizer ({v.val} : Set (Carrier (binaryParameters m hm)))),
      (R : Subgroup _) = (unipotent (binaryParameters m hm)).subgroupOf
        (centralizer ({v.val} : Set (Carrier (binaryParameters m hm))))) :
    let x : G := (e.right.symm v).val
    ∃ R : Sylow 2 (centralizer ({x} : Set G)),
      (R : Subgroup _) = (T : Subgroup G).subgroupOf (centralizer ({x} : Set G)) :=
  d.triality_involution_centralizer_sylow (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m hm e v hv hv2 hmodel

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Exact triality Sylow-centralizer orders for the Chapter 12 pair

The two trace equations on the genuine positive subgroup give the exact
short-root count q¹⁰. Transport through the original right map and the
proved S=T give q¹² and q¹⁰ for the two marked centralizers in T.
The full ambient centralizers and final recognition remain separate duties.

Source: Aschbacher--Smith F.4.27, F.4.38 and F.4.40, printed pp.288--289,
294, and 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The marked short root has exactly q¹⁰ centralizing elements in the original S. -/
theorem rankOne_global_triality_short_source_centralizer_card
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    let P := binaryParameters m hm
    let v : G := (e.right.symm (Global.TrialityCompletionFusion.shortElement P rfl)).val
    Nat.card (Global.sourceS L H ⊓ centralizer ({v} : Set G) : Subgroup G) = P.q^10 :=
  d.triality_short_source_centralizer_card (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 m hm e

/-- Exact long and short counts in T, including q=4, with S=T discharged. -/
theorem rankOne_global_triality_marked_sylow_centralizer_card
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
    let z : G := (e.right.symm (Global.TrialityCompletionFusion.longElement P rfl)).val
    let v : G := (e.right.symm (Global.TrialityCompletionFusion.shortElement P rfl)).val
    Nat.card ((T : Subgroup G) ⊓ centralizer ({z} : Set G) : Subgroup G) = P.q^12 ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Subgroup G) = P.q^10 :=
  d.triality_marked_sylow_centralizer_card (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m hm e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.TrialityAllDegrees
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalTrialityExtension

/-!
# Reduced exceptional and binary triality sieves in Chapter 12

The chosen-module hypotheses force both reduced endpoints to be nonsolvable.
Every actual exceptional parabolic comparison, including J₂ and Aut(J₂),
is excluded in either orientation. Binary triality is excluded by its central
endpoint, and all other triality degrees give the original comparison and
same-S containment through the existing restoration.

Source: DGS (1985), (15.2)–(15.3), pp.226–231; Aschbacher–Smith 5.2.6,
pp.650–651, and the Chapter 12 chosen-module argument, p.795.
No recognition is inferred from binary Ree structural type data.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.DGS85.OriginalExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
include D h hmany hn hpsl hH

/-- Exclude all eight reduced exceptional parabolic rows for the same
arbitrary perfect selected R, including both Hall–Janko rows. -/
theorem rankOne_global_not_reduced_exceptional
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) (c : ChapterF.GreenBook.ExceptionalModels.Case) :
    ¬ (ChapterF.GreenBook.ExceptionalModels.ParabolicModel c
        (reducedAmalgam ![L,R] (Global.sourceS L H)) ∨
      ChapterF.GreenBook.ExceptionalModels.ParabolicModel c
        (reducedAmalgam ![L,R] (Global.sourceS L H)).reverse) :=
  not_reduced_exceptional_parabolicModels d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp c

/-- All positive triality degrees now give the original comparison, with
binary exclusion discharged before invoking native restoration. -/
theorem rankOne_global_comparison_of_reduced_triality_all_degrees
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) (m : ℕ) (hm : 0 < m) (i : Bool)
    (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) (TrialityNative.amalgam m hm i)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  concreteComparison_of_reduced_triality_all_degrees d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm i e

/-- The same all-degree application supplies the literal original core and
containment premises, without replacing S or the chosen perfect R. -/
theorem rankOne_global_core_and_containment_of_reduced_triality_all_degrees
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) (m : ℕ) (hm : 0 < m) (i : Bool)
    (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) (TrialityNative.amalgam m hm i)) :
    (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R :=
  triality_original_core_and_containment_all_degrees d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm i e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

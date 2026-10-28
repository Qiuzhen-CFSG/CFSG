module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.UnitaryFiveNativeApplication
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalUnitaryFiveExtension

/-!
# Reduced U₅ restoration at the Chapter 12 chosen module

The chosen-module preparation gives genuine F.1.1 on the original S and
selected perfect R. A marked reduced U₅(q) pair, in either orientation,
therefore yields the original comparison and original core equalities.
When the selected R is the residual, the constructed original marking also
feeds the existing prepared completion and gives the actual GlobalExit.

The original normalization and quasithin hypotheses perform the field and
outer-action sieves. Neither q = 4 nor an original marked comparison is an
input. Exhaustive reduced recognition remains with source assembly.
Source: DGS (1985), (15.2), pp.226–228; Aschbacher–Smith F.1.12, pp.263–264,
and the Chapter 12 chosen-module application, p.795.
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

/-- Every even-prime-power reduced U₅ marking gives the literal original
comparison for the same perfect selected factor. -/
theorem rankOne_global_comparison_of_reduced_unitaryFive
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) {q : ℕ} (hq : IsPrimePow q) (heven : Even q)
    (M : ChapterF.GreenBook.UnitaryFive.Model q) (line : Bool)
    (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) (UnitaryFiveNative.amalgam M line)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  concreteComparison_of_reduced_unitaryFive d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hq heven M line e

/-- The reduced comparison now proves containment of the original S and
both original core equalities in the chosen-module application. -/
theorem rankOne_global_collapse_of_reduced_unitaryFive
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) {q : ℕ} (hq : IsPrimePow q) (heven : Even q)
    (M : ChapterF.GreenBook.UnitaryFive.Model q) (line : Bool)
    (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) (UnitaryFiveNative.amalgam M line)) :
    Global.sourceS L H ≤ R ∧ Global.sourceS L H ≤ L ∧
      (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧
      (L ⊔ Global.sourceS L H).pCoreIn 2 = L.pCoreIn 2 :=
  unitaryFive_original_collapse_of_reduced_iso d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hq heven M line e

/-- On the residual preparation, reduced recognition suffices for the
existing actual completion and GlobalExit; its original marking is constructed. -/
theorem rankOne_globalExit_of_reduced_unitaryFive
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) {q : ℕ} (hq : IsPrimePow q) (heven : Even q)
    (M : ChapterF.GreenBook.UnitaryFive.Model q) (line : Bool)
    (e : Iso (reducedAmalgam ![L,residual H] (Global.sourceS L H))
      (UnitaryFiveNative.amalgam M line)) : RankOneModule.GlobalExit G := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hq4 := UnitaryFiveNative.field_eq_four_of_reduced_iso
    hi.qtke.quasithin hq heven M line e
  subst q
  obtain ⟨f⟩ := exists_original_unitaryFive_marking_of_reduced_iso
    hi.qtke.quasithin (d.hypothesisF11 hi hH.1.1.2) hq heven M line e
  exact D.rankOne_globalExit_of_original_unitaryFive h hmany hn hpsl hH d hp
    hq heven M line (ChapterF.SourceCompletion.UnitaryNonbinary.five_conj_injective M) f

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

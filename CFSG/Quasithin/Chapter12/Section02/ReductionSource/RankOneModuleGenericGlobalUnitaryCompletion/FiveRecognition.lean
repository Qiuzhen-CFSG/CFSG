module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.FiveRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryCompletion.Defect

/-!
# The actual Chapter 12 PSU₅(4) recognition exit

At W = wholeReduced T L, the actual normalizer-pair comparison, compatible
DGS extension, and ambient order bound identify G as PSU₅(4). The GlobalExit
uses unitary exponent two, while the original rank-one exponent is four.
Both comparison orientations and the projective scalar kernel are retained.

Source: Aschbacher–Smith 5.3.1–4, F.4.24 and Chapter12, pp.658–659,287,795.
The generic-global owner retains construction of the explicit source inputs
and exhaustion of the comparison rows.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
open ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

theorem rankOne_unitaryFive_extension_recognition (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : FiveLocalComparison L (residual H) (Global.sourceS L H) U)
    (E : FiveExtension U) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    n = 4 ∧ Nat.card G=Nat.card E.carrier ∧ ClassicalGroup.IsPSU G 5 4 := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_extension_recognition hi hH hp U hc E he horder

/-- Close the actual parameter-four unitary-five recognition row at the actual whole reduced module. -/
theorem rankOne_globalExit_of_unitaryFive_extension (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : FiveLocalComparison L (residual H) (Global.sourceS L H) U)
    (E : FiveExtension U) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) : RankOneModule.GlobalExit G := by
  obtain ⟨_,_,hpsu⟩ := D.rankOne_unitaryFive_extension_recognition h hmany hn hpsl hH d hp U hc E he horder
  exact Or.inl ⟨2,by decide,ClassificationModels.IsRankTwoModel.unitary_five rfl hpsu⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

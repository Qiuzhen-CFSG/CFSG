module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.FourRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryCompletion.Defect

/-!
# The actual Chapter 12 unitary-four recognition exit

At W = wholeReduced T L the original normalizer-pair comparison, genuine
compatible DGS extension and full ambient order bound identify G as
PSU₄(2^m), with m > 1 and n = 2*m. The GlobalExit uses the strict unitary
exponent m, including m = 2 and the degree-two local comparison.

Source: Aschbacher–Smith 5.3.1–4, F.4.24 and Chapter12, pp.658–659,287,795.
The generic-global owner retains construction of the extension and order
inputs and exhaustion of the comparison rows. The PSU₅(4) row is separate.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
open ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

theorem rankOne_unitary_extension_recognition (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
    (E : FourExtension m hm) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    1 < m ∧ n = 2*m ∧ Nat.card G=Nat.card E.carrier ∧ ClassicalGroup.IsPSU G 4 (2^m) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_extension_recognition hi hH hp m hm hc E he horder

/-- Close the U₄ ordinary and degree-two recognition rows at the actual whole reduced module. -/
theorem rankOne_globalExit_of_unitary_extension (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
    (E : FourExtension m hm) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) : RankOneModule.GlobalExit G := by
  obtain ⟨hmgt,_,_,hpsu⟩ := D.rankOne_unitary_extension_recognition h hmany hn hpsl hH d hp m hm hc E he horder
  exact Or.inl ⟨m,hmgt,ClassificationModels.IsRankTwoModel.unitary_four hm hpsu⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

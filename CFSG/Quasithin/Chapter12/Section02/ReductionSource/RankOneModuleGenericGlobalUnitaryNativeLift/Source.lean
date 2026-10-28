module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryNativeLift.Source
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.MarkedAction

/-!
# Faithful native unitary lifts for the literal whole reduced module

The original chosen-module input, with W = wholeReduced T L, supplies the
faithful coherent native automorphism actions in both unitary rows and both
orientations. Every original proper-K, catalogue and ambient hypothesis is
retained. The degree-two comparison uses the same full actor and the five-row
uses its actual projective carrier, with no new restriction-image premise.

Source: Aschbacher–Smith 12.2.22, printed p.795, and the realization step
of 5.3.2, printed p.659. Ambient transfer and final source recognition remain
with their source assembly owners.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Native lifting of the original four-dimensional whole-reduced-module action,
including the degree-two original comparison, in both orientations. -/
theorem rankOne_unitary_native_lifted_middle_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {A C : Subgroup G} (d : Preparation T L H A C (residual H))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
      ((∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
          (amalgam m hm), Nonempty (UnitaryNativeLift.Four.Lift m hm a)) ∨
       (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
          (amalgam m hm).reverse, Nonempty (UnitaryNativeLift.Four.LiftReverse m hm a))) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_native_lifted_middle_action hi hH hp m hm hc

/-- Native lifting of the original projective five-dimensional
whole-reduced-module action, in both orientations. -/
theorem rankOne_unitaryFive_native_lifted_middle_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {A C : Subgroup G} (d : Preparation T L H A C (residual H))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
        U.amalgam, Nonempty (UnitaryNativeLift.Five.Lift U a)) ∨
    (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
        U.amalgam.reverse, Nonempty (UnitaryNativeLift.Five.LiftReverse U a)) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_native_lifted_middle_action hi hH hp U hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedCentralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four

/-!
# Original chosen-module marked centralizer comparisons

Apply the source argument to the whole reduced module and the existing
named extension of the original prepared row. The actual endpoint map
identifies each full ambient long-root centralizer with the centralizer
in that same extension. Its other endpoint identifies the local short-root
centralizer with the full extension short-root centralizer. The entire
middle action and carrier remain the same in both comparisons.
No centralizer, transfer or order-comparison premise is added.

Source: Aschbacher–Smith F.4.42–43, pp.295–296, applied at 5.3.3/12.2.22.
Short-root fixed cosets, outer transfer and final ambient order remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open Global.UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Long and short centralizer isomorphisms through the same original
marking, including every original right-center involution. -/
theorem rankOne_unitaryFour_marked_centralizers (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm) :
    let r := D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc
    (∃ a : Global.UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) (amalgam m hm).reverse,
      ∃ f : Global.UnitaryNativeLift.Four.LiftReverse m hm a,
      ∃ F : RankTwoAmalgam.Iso (Global.UnitaryCompletion.normalizerDiagram L (residual H)) r.extension.amalgam.reverse,
        (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        Global.UnitarySource.FourLongCentralizerComparison r F ∧
        Global.UnitarySource.FourShortCentralizerComparison r a F) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFour_marked_centralizers hi hH hp m hm hc
    (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

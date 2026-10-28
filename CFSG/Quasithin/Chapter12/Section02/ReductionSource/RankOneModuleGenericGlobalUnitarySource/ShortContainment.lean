module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortContainment
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four

/-!
# Full ambient short-root containment for the original unitary row

Apply both stages of F.4.42 to the original whole-reduced chosen module.
The maximal-W Bender alternative is excluded by the actual perfect actor
containing its whole short-root line. The conclusion bounds the full
ambient centralizer, with no fusion, unique-fixed-coset, odd-core or
perfect-actor premises. Both orientations, degree-two rows and q=4 remain.

Odd outer degree on the same named full-normalizer extension remains the
explicit F.4.38 premise. Source: Aschbacher–Smith F.4.42, pp.295–296,
applied at 5.3/12.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Both full ambient root centralizers, on the original chosen module's
named extension and exact endpoint and overlap maps, after odd outer degree. -/
theorem rankOne_unitaryFour_ambient_centralizers_of_odd_outer
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex
      (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc).extension.carrier) :
    let r := D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc
    ∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) (amalgam m hm).reverse,
      ∃ f : UnitaryNativeLift.Four.LiftReverse m hm a,
      ∃ F : RankTwoAmalgam.Iso (normalizerDiagram L (residual H)) r.extension.amalgam.reverse,
        (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        UnitarySource.FourLongCentralizerComparison r F ∧
        UnitarySource.FourAmbientShortCentralizerComparison r a F := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFour_ambient_centralizers_of_odd_outer hi hH hp m hm hc
    (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc) hodd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

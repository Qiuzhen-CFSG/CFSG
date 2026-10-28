module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.InnerReturn
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four

/-!
# Inner returns in the original chosen-module unitary row

Use the named full-normalizer extension for the whole reduced chosen module.
Ambient long-root returns with inner endpoint image belong to the original
left two-core. Odd degree over that same inner group puts all two-subgroups
of the full left normalizer in the original residual, and hence identifies
the ambient and reduced Sylows. The odd-degree premise is F.4.38; it still
requires the ambient outer-transfer proof.

Source: Aschbacher–Smith F.4.35–38,42, pp.292–295, applied at 5.3/12.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Inner-image returns through the same original full-normalizer marking. -/
theorem rankOne_unitary_long_inner_return
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    let r := D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc
    ∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) (amalgam m hm).reverse,
    ∃ f : UnitaryNativeLift.Four.LiftReverse m hm a,
    ∃ F : RankTwoAmalgam.Iso (normalizerDiagram L (residual H)) r.extension.amalgam.reverse,
      (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (f.action z).val) ∧
      ∀ z ∈ (center (residual H)).map (residual H).subtype, orderOf z = 2 →
        ∀ x : normalizer (L : Set G), IsConj z x.val →
          (F.left x).val ∈ inner (ProjectiveGroup m hm) → x.val ∈ L.pCoreIn 2 := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_long_inner_return hi hH hp m hm hc
    (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc)

/-- F.4.38's precise parity conclusion identifies the original Sylow,
without discarding degree-two rows or replacing the marked extension. -/
theorem rankOne_unitaryFour_two_subgroups_of_odd_outer
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
    (∀ S : Subgroup G, IsPGroup 2 S → S ≤ normalizer (L : Set G) → S ≤ L) ∧
      (T : Subgroup G) ⊓ L = T := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFour_two_subgroups_of_odd_outer hi hH hp m hm hc
    (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc) hodd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

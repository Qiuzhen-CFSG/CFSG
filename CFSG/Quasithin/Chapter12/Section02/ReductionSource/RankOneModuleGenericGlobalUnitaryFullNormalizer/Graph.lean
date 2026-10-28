module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.Graph
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four

/-!
# The original graph element in the chosen-module unitary-four extension

The literal whole-reduced input supplies the graph involution on the same
constructed extension used by the order-only recognition consumer. Both
orientations retain the endpoint and entire common-normalizer equations.
Source: Aschbacher–Smith 5.3.2 and F.4.37, printed pp.659 and293.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
open ChapterF.SourceCompletion.UnitaryNonbinary
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The degree-two graph involution remains outer in the fixed extension. -/
theorem rankOne_unitaryFour_constructed_graph (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm).reverse)) :
    let M := D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm (Or.inr hc)
    1 < m ∧ n = 2*m ∧ ∃ g : G,
      g ∈ Global.sourceS L H ∧ g ∈ (T : Subgroup G) ∧ orderOf g = 2 ∧
      g ∉ L ∧ g ∉ residual H ∧
      ∃ hg : g ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G),
      (∃ a : Global.UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) (amalgam m hm),
        ∃ f : Global.UnitaryNativeLift.Four.Lift m hm a,
        ∃ F : RankTwoAmalgam.Iso (normalizerDiagram L (residual H)) M.extension.amalgam,
        (∀ x, (F.left (inclusion M.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion M.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        orderOf (F.middle ⟨g,hg⟩) = 2 ∧ (F.middle ⟨g,hg⟩).val ∉
          ChapterF.SourceCompletion.UnitaryNonbinary.inner (ProjectiveGroup m hm)) ∨
      (∃ a : Global.UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) (amalgam m hm).reverse,
        ∃ f : Global.UnitaryNativeLift.Four.LiftReverse m hm a,
        ∃ F : RankTwoAmalgam.Iso (normalizerDiagram L (residual H)) M.extension.amalgam.reverse,
        (∀ x, (F.left (inclusion M.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion M.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        orderOf (F.middle ⟨g,hg⟩) = 2 ∧ (F.middle ⟨g,hg⟩).val ∉
          ChapterF.SourceCompletion.UnitaryNonbinary.inner (ProjectiveGroup m hm)) :=
  d.unitaryFour_constructed_graph (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

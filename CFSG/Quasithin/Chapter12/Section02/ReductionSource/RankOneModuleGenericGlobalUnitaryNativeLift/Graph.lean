module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryNativeLift.Graph
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryNativeLift.Source

/-!
# The original graph involution in the lifted Chapter12 action

Apply the degree-two native lift to the literal whole-reduced-module input.
The same original ambient element has order two and lies outside the native
Borel conjugation image in either orientation. Source: Aschbacher–Smith
12.2.22 and 5.3.2, printed pp.795,659.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Theory.SpecificGroups.ClassicalUnitary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The literal chosen module retains the original graph involution in its
faithful native lift, without changing the original Sylow or sourceS. -/
theorem rankOne_unitary_graph_native_lifted_middle_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {A C : Subgroup G} (d : Preparation T L H A C (residual H))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧ ∃ g : G,
      g ∈ sourceS L H ∧ g ∈ (T : Subgroup G) ∧ orderOf g = 2 ∧
      g ∉ L ∧ g ∉ residual H ∧
      ∃ hg : g ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G),
        (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
            (amalgam m hm), ∃ f : UnitaryNativeLift.Four.Lift m hm a,
          orderOf (f.action ⟨g,hg⟩) = 2 ∧
          f.action ⟨g,hg⟩ ∉ (NativeAmalgamActions.innerMiddle (pointParabolic m hm)
            (planeParabolic m hm) (overlap m hm) (Subgroup.map_mono inf_le_left)
            (Subgroup.map_mono inf_le_right)).range) ∨
        (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
            (amalgam m hm).reverse, ∃ f : UnitaryNativeLift.Four.LiftReverse m hm a,
          orderOf (f.action ⟨g,hg⟩) = 2 ∧
          f.action ⟨g,hg⟩ ∉ (NativeAmalgamActions.innerMiddle (pointParabolic m hm)
            (planeParabolic m hm) (overlap m hm) (Subgroup.map_mono inf_le_left)
            (Subgroup.map_mono inf_le_right)).range) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_graph_native_lifted_middle_action hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

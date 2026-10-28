module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryNativeLift.Source

/-!
# The degree-two graph involution survives native lifting

Faithful exact restriction retains the original graph element with order two
and outside the native Borel conjugation image. Apply this to the existing
source graph-element theorem, without changing sourceS or the ambient Sylow.
Source: the degree-two case in Aschbacher–Smith 5.3.2 and F.4.37,
printed pp.659,293.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Theory.SpecificGroups.ClassicalUnitary
namespace UnitaryNativeLift.Four
variable {G : Type*} [Group G] {L K S : Subgroup G} {m : ℕ} {hm : 1 ≤ m}

/-- A non-Borel-inner involution of the marked action remains such after lifting. -/
theorem graph_involution {a : UnitarySource.MarkedMiddleAction L K S (amalgam m hm)}
    (f : Lift m hm a) (g)
    (ho : orderOf (a.action g) = 2)
    (hn : a.action g ∉ (UnitarySource.innerMiddle (amalgam m hm)).range) :
    orderOf (f.action g) = 2 ∧
      f.action g ∉ (NativeAmalgamActions.innerMiddle (pointParabolic m hm)
        (planeParabolic m hm) (overlap m hm) (Subgroup.map_mono inf_le_left)
        (Subgroup.map_mono inf_le_right)).range := by
  constructor
  · exact (orderOf_injective f.action f.faithful g).trans
      ((orderOf_injective a.action a.faithful g).symm.trans ho)
  · rintro ⟨b, hb⟩
    apply hn
    refine ⟨b, ?_⟩
    have he := congrArg (Chapter5.UnitaryNativeLift.Four.restriction m hm) hb
    refine (show UnitarySource.innerMiddle (amalgam m hm) b =
      Chapter5.UnitaryNativeLift.Four.restriction m hm
        (NativeAmalgamActions.innerMiddle (pointParabolic m hm)
          (planeParabolic m hm) (overlap m hm) (Subgroup.map_mono inf_le_left)
          (Subgroup.map_mono inf_le_right) b) from ?_).trans
      (he.trans (DFunLike.congr_fun f.restriction_eq g))
    apply RankTwoAmalgam.Iso.ext <;> ext x <;> rfl

/-- A non-Borel-inner involution of the marked action remains such after lifting. -/
theorem graph_involutionReverse {a : UnitarySource.MarkedMiddleAction L K S (amalgam m hm).reverse}
    (f : LiftReverse m hm a) (g)
    (ho : orderOf (a.action g) = 2)
    (hn : a.action g ∉ (UnitarySource.innerMiddle (amalgam m hm).reverse).range) :
    orderOf (f.action g) = 2 ∧
      f.action g ∉ (NativeAmalgamActions.innerMiddle (pointParabolic m hm)
        (planeParabolic m hm) (overlap m hm) (Subgroup.map_mono inf_le_left)
        (Subgroup.map_mono inf_le_right)).range := by
  constructor
  · exact (orderOf_injective f.action f.faithful g).trans
      ((orderOf_injective a.action a.faithful g).symm.trans ho)
  · rintro ⟨b, hb⟩
    apply hn
    refine ⟨b, ?_⟩
    have he := congrArg (Chapter5.UnitaryNativeLift.Four.reverseRestriction m hm) hb
    refine (show UnitarySource.innerMiddle (amalgam m hm).reverse b =
      Chapter5.UnitaryNativeLift.Four.reverseRestriction m hm
        (NativeAmalgamActions.innerMiddle (pointParabolic m hm)
          (planeParabolic m hm) (overlap m hm) (Subgroup.map_mono inf_le_left)
          (Subgroup.map_mono inf_le_right) b) from ?_).trans
      (he.trans (DFunLike.congr_fun f.restriction_eq g))
    apply RankTwoAmalgam.Iso.ext <;> ext x <;> rfl

end UnitaryNativeLift.Four

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The original degree-two graph element remains an involution outside the
native Borel-inner image in the actual lifted source action. -/
theorem Preparation.unitary_graph_native_lifted_middle_action
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
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
  obtain ⟨hmgt, hn, g, hgs, hgt, hgo, hgl, hgk, hg, ha⟩ :=
    d.unitary_graph_native_middle_action h hH hp m hm hc
  refine ⟨hmgt, hn, g, hgs, hgt, hgo, hgl, hgk, hg, ?_⟩
  rcases ha with ha | ha <;> obtain ⟨a, ho, hb⟩ := ha
  · let f := UnitaryNativeLift.Four.lift m hm hmgt a
    exact Or.inl ⟨a, f, UnitaryNativeLift.Four.graph_involution f _ ho hb⟩
  · let f := UnitaryNativeLift.Four.liftReverse m hm hmgt a
    exact Or.inr ⟨a, f, UnitaryNativeLift.Four.graph_involutionReverse f _ ho hb⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

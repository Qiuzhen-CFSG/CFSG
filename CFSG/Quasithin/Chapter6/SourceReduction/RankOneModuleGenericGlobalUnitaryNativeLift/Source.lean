module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryNativeLift.Actions

/-!
# Native unitary realization in the original Chapter 6 input

Apply exact native lifting to the published common-normalizer actions.
The four-dimensional comparison includes the original degree-two extension;
its reduction to the native pair changes neither the ambient Sylow nor the
actor. Both orientations and the projective U₅(4) row are retained. The output
contains the original marked action together with its faithful coherent lift,
whose endpoint, middle and Borel conjugation equations are proved in Actions.

Source: Aschbacher–Smith 5.3.1–2, printed pp.658–659. This removes the
restriction-image premise in the realization step, independently of source
join recognition, outer transfer, and full-normalizer endpoint gluing.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The original input supplies the faithful native lift, also for the original
degree-two comparison; no extension-image hypothesis remains. -/
theorem Preparation.unitary_native_lifted_middle_action
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
      ((∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
          (amalgam m hm), Nonempty (UnitaryNativeLift.Four.Lift m hm a)) ∨
       (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
          (amalgam m hm).reverse, Nonempty (UnitaryNativeLift.Four.LiftReverse m hm a))) := by
  obtain ⟨hmgt, hn, ha⟩ := d.unitary_native_middle_action h hH hp m hm hc
  refine ⟨hmgt, hn, ?_⟩
  rcases ha with ha | ha <;> obtain ⟨a⟩ := ha
  · exact Or.inl ⟨a, ⟨UnitaryNativeLift.Four.lift m hm hmgt a⟩⟩
  · exact Or.inr ⟨a, ⟨UnitaryNativeLift.Four.liftReverse m hm hmgt a⟩⟩

/-- The actual projective five-dimensional input supplies the faithful native
lift in either orientation, retaining its scalar kernel of order five. -/
theorem Preparation.unitaryFive_native_lifted_middle_action
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
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
  rcases d.unitaryFive_native_middle_action h hH hp U hc with ha | ha <;> obtain ⟨a⟩ := ha
  · exact Or.inl ⟨a, ⟨UnitaryNativeLift.Five.lift U a⟩⟩
  · exact Or.inr ⟨a, ⟨UnitaryNativeLift.Five.liftReverse U a⟩⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

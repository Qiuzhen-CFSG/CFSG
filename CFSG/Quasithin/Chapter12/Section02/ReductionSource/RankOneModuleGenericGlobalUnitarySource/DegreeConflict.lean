module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.DegreeConflict
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryCompletion

/-!
# Literal chosen-module consumer for the unitary degree-two obstruction

At the whole reduced module, the actual degree-two row forces even outer
degree on the same constructed full-normalizer extension. This retains the
original preparation, both orientations and the entire projective graph map.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterF.SourceCompletion.UnitaryNonbinary
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The actual whole-reduced-module adapter for the even outer-index
consequence of a degree-two U₄ comparison. -/
theorem rankOne_unitaryFour_degreeTwo_outer_index_even
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (Extension.amalgam m hm).reverse)) :
    2 ∣ (ChapterF.SourceCompletion.UnitaryNonbinary.inner (ProjectiveGroup m hm)).relIndex
      (d.unitaryFourNormalizerMarking
        (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm
        (Or.inr hc)).extension.carrier := by
  exact d.unitaryFour_degreeTwo_outer_index_even
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

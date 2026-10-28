module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.InnerSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# F.4.38 in the original chosen-module U₅(4) branch

Apply the full fixed-Sylow argument and the actual selected-actor
representation to the marking constructed for this original row.
The conclusion concerns the original S and T. The later short-centralizer
and order arguments are separate obligations.
Source: 12.2.22 and F.4.37–38, printed pp.795,293–294 of refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The original chosen-module Sylow has no outer actor. -/
theorem rankOne_unitaryFive_sourceS_eq_sylow
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    sourceS L H = (T : Subgroup G) := by
  exact d.unitaryFive_sourceS_eq_sylow (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp U hc (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

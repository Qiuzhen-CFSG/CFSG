module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.OddOuter
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.InnerSylow

/-!
# Odd outer degree and inner returns in the chosen U₅(4) branch

The actual original marking has odd outer degree. Every two-subgroup of
the original plane normalizer lies in L. These are applications of the
proved S=T statement, with no actor-representation or parity premise.
Source: 12.2.22 and F.4.38,42, printed pp.795,294–296 of refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Odd degree of the same full-normalizer extension in the original row. -/
theorem rankOne_unitaryFive_outer_odd
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
    let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
    ¬ 2 ∣ (inner U.Carrier).relIndex r.extension.carrier := by
  exact d.unitaryFive_outer_odd (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp U hc (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc)

/-- All two-subgroups of the original plane normalizer lie in L. -/
theorem rankOne_unitaryFive_normalizer_two_subgroup_le_left
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
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (P : Subgroup G) (hP : IsPGroup 2 P) (hPN : P ≤ normalizer (L : Set G)) :
    P ≤ L := by
  exact d.unitaryFive_normalizer_two_subgroup_le_left
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc
    (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc) P hP hPN

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

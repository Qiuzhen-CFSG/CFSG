module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FieldTransfer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# U₅(4) cyclic transfer in the original chosen-module row

The whole-reduced Chapter 12 input supplies the source theorem with its
original KnownSimple, many-overgroups, PSL₂, maximal-normalizer and whole
residual hypotheses. It gives the actual source-Sylow index bound and fuses
each ambient involution into the same original S. This does not claim S=T or
replace the remaining ambient involution-class and centralizer arguments.

Source: Aschbacher–Smith F.4.35–38 and 5.3.3, applied in Chapter 12,
printed pp.292–294,659,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The original source-Sylow index divides four in the U₅(4) row. -/
theorem rankOne_global_unitaryFive_source_sylow_index_dvd
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam.reverse)) :
    (Global.sourceS L H).relIndex (T : Subgroup G) ∣ 4 := by
  exact d.unitaryFive_source_sylow_index_dvd
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc

/-- Every ambient involution is conjugate into the actual original source S. -/
theorem rankOne_global_unitaryFive_involution_fused_into_sourceS
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam.reverse))
    (x : G) (hx : orderOf x = 2) :
    ∃ y ∈ Global.sourceS L H, IsConj x y := by
  exact d.unitaryFive_involution_fused_into_sourceS
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc x hx

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

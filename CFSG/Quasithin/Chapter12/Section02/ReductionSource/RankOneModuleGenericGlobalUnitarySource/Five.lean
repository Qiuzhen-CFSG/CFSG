module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Five
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.Completion

/-!
# Original chosen-module U₅ source input

The whole-reduced chosen module supplies the original KnownSimple input to
the prepared U₅ source producer. It constructs the actual full-normalizer
extension, keeps both endpoint markings and the whole overlap, and discharges
the same-extension order comparison. The existing Chapter12 completion and
recognition then give the original PSU₅(4) row without any extra source
premises.

Source: Aschbacher–Smith 5.3.1–4, F.4.42–44 and Chapter12, printed
pp.658–659,295–296,795 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
open ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- At the literal whole-reduced module, the prepared comparison constructs
the full-normalizer U₅ extension and supplies its same-carrier order bound. -/
theorem rankOne_unitaryFive_source
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
    ∃ E : FiveExtension U, Compatible L (residual H) E ∧
      Nat.card G ≤ Nat.card E.carrier := by
  let hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_source hi hH hp U hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

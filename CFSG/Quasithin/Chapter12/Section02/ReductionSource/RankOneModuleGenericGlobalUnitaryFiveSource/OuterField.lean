module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.OuterField
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Outer-involution quotient coordinates in the chosen unitary-five row

Build the original whole-reduced Input and identify its literal L/O₂(L)
quotient with PSL₂(16). Every original involution outside S has coefficient
x ↦ x⁴ and an actual quotient conjugator to that field action. This is the
quotient restriction required by F.4.29(2), not a full PSU₅ representation.
Source: F.4.29(2) and 12.2.22, printed pp.289,795 of refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The full original Sylow acts on the original quotient in these coordinates. -/
theorem rankOne_unitaryFive_outer_involution_quotient_coordinates (D : ChosenModule T L V)
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
    let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
    ∃ e : (L ⧸ pCore 2 L) ≃* Theory.PSL2.BinaryGroup 4,
      ∀ (t : T), orderOf t=2 → t.val∉sourceS L H →
        (∀ x : Theory.PSL2.BinaryField 4,
          unitaryFiveSylowFieldAction hi.sylow_normalizes e t x=x^4) ∧
        ∃ c : Theory.PSL2.BinaryGroup 4,
          MulAut.congr (MulAut.conj c) (Theory.PSL2.fieldAut (Theory.PSL2.binaryHalfFrobenius 4)) =
            MulAut.congr e (pCoreJoinAction 2 hi.sylow_normalizes (inclusion le_sup_right t)) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_outer_involution_quotient_coordinates hi hH hp U hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveActor.MarkedCoefficient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# The native quotient coefficient of the chosen original U₅ actor

The original chosen-module hypotheses supply the full whole-reduced input.
Apply the residual commuting square to the same reversed action, lift and
full-normalizer marking. This gives the involution and Hermitian-coefficient
inputs for every original outer involution in that middle, including the
saturated choice. Full actor representation is still required.

Source: Aschbacher–Smith F.4.29(2) and 12.2.22, pp.289,795 of refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.UnitaryFiveFlagAutomorphisms
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The same original chosen actor satisfies the native coefficient condition. -/
theorem rankOne_unitaryFive_marked_actor_coefficient (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
      U.amalgam.reverse)
    (ell : UnitaryNativeLift.Five.LiftReverse U a)
    (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
      r.extension.amalgam.reverse)
    (hF : ∀ z, (F.middle z).val = (ell.action z).val)
    (t : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
    (htT : t.val ∈ (T : Subgroup G)) (ht : orderOf t = 2)
    (htS : t.val ∉ sourceS L H) :
    (ell.action t).val = (F.middle t).val ∧
      (ell.action t) ^ 2 = 1 ∧ rightCoefficient U (ell.action t) = U.form.conj := by
  exact d.unitaryFive_marked_actor_coefficient
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc r a ell F hF t htT ht htS

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

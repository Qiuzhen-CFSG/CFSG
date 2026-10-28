module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.OddRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four

/-!
# Original chosen-module U₄ recognition and exit at odd ordinary degree

At the literal whole reduced module, construct the full-normalizer extension,
prove its ambient order equality and apply the independent completion
recognizer. The resulting original-group PSU₄ identification supplies GlobalExit
with exponent m > 1. The full KnownSimple catalogue and proper-K hypotheses
are inherited from the original chosen-module input, in both orientations.

Source: Aschbacher--Smith 5.3.2--4, F.4.43 and 12.2, pp.659,296,795.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}
variable (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse))
include D h hmany hn hpsl hH d hp hc

/-- At the literal whole reduced module, construct the full extension and
prove its ambient order bound from the ordinary odd-degree comparison. -/
theorem rankOne_unitaryFour_ordinary_source_of_odd (hmOdd : Odd m) :
    ∃ E : FourExtension m hm, Compatible L (residual H) E ∧
      Nat.card G ≤ Nat.card E.carrier :=
  d.unitaryFour_ordinary_source_of_odd
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc hmOdd

/-- The published completion-input theorem at the literal whole reduced
module, with its source extension and ambient order premise now discharged. -/
theorem rankOne_unitaryFour_ordinary_completion_of_odd (hmOdd : Odd m) :
    let E := (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm (Or.inl hc)).extension
    1 < m ∧ n = 2*m ∧
      ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
          (G := NormalizerJoin L (residual H)),
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Nat.card (NormalizerJoin L (residual H)) ≤ Nat.card E.carrier ∧
        ∀ i : Bool, Nat.card (NormalizerJoin L (residual H) ⧸ c.cosetFamily i) ≤
          Nat.card (ProjectiveGroup m hm ⧸ SourceExtension.nativeFamily
            (P₀ := pointParabolic m hm) (P₁ := planeParabolic m hm) i) :=
  d.unitaryFour_ordinary_completion_of_odd
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc hmOdd

/-- Recognition of the original ambient group, with no realization, parity,
fusion, centralizer or order callback in the ordinary odd-degree branch. -/
theorem rankOne_unitaryFour_ordinary_recognition_of_odd (hmOdd : Odd m) :
    1 < m ∧ n = 2*m ∧ Nat.card G = Nat.card
      (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm (Or.inl hc)).extension.carrier ∧
      ClassicalGroup.IsPSU G 4 (2^m) :=
  d.unitaryFour_ordinary_recognition_of_odd
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc hmOdd

/-- The original chosen-module U₄ row has GlobalExit at odd ordinary degree;
all source inputs are discharged, and the exit retains exponent m > 1. -/
theorem rankOne_globalExit_of_unitaryFour_ordinary_odd (hmOdd : Odd m) :
    RankOneModule.GlobalExit G :=
  D.rankOne_globalExit_of_unitaryFour_constructed h hmany hn hpsl hH d hp m hm (Or.inl hc)
    (d.unitaryFour_ordinary_order_of_odd
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc hmOdd _).le

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

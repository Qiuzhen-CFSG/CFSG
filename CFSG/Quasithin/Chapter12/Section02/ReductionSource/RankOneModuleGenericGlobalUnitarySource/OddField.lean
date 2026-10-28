module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.OddField
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four

/-!
# Discharging outer parity at odd ordinary degree for the chosen module

On the literal whole reduced module, the right quotient gives the ordinary
Sylow index dividing m. Odd m makes sourceS the entire original T, proves
odd outer degree on the same named full-normalizer extension, and supplies
both full ambient root-centralizer comparisons. No parity, fusion or
centralizer premise is retained in this specialized ordinary branch.

The other degree and comparison branches remain in the general source
family. Source: Aschbacher--Smith F.4.38,42 and the original 5.3/12.2
application, printed pp.294--296,659,795 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
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
include D h hmany hn hpsl hH d hp hm hc

/-- The ordinary unitary degree, rather than the original exponent n=2m,
controls the original Sylow/source index. -/
theorem rankOne_unitaryFour_ordinary_sylow_index_dvd :
    (sourceS L H).relIndex (T : Subgroup G) ∣ m :=
  d.unitaryFour_ordinary_sylow_index_dvd
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc

/-- Odd ordinary degree proves ambient Sylow equality and the required parity
on the original chosen-module construction, with both orientations retained. -/
theorem rankOne_unitaryFour_ordinary_sylow_and_outer_odd (hmOdd : Odd m) :
    sourceS L H = (T : Subgroup G) ∧
      ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex
        (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm (Or.inl hc)).extension.carrier := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.unitaryFour_ordinary_sourceS_eq_sylow_of_odd hi hH hp m hm hc hmOdd,
    d.unitaryFour_ordinary_outer_odd_of_odd hi hH hp m hm hc hmOdd
      (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm (Or.inl hc))⟩

/-- Both full ambient centralizers on the same named extension, with outer
parity now discharged in the ordinary odd-degree branch. -/
theorem rankOne_unitaryFour_ordinary_ambient_centralizers_of_odd (hmOdd : Odd m) :
    let r := D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm (Or.inl hc)
    ∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) (amalgam m hm).reverse,
      ∃ f : UnitaryNativeLift.Four.LiftReverse m hm a,
      ∃ F : RankTwoAmalgam.Iso (normalizerDiagram L (residual H)) r.extension.amalgam.reverse,
        (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        UnitarySource.FourLongCentralizerComparison r F ∧
        UnitarySource.FourAmbientShortCentralizerComparison r a F :=
  d.unitaryFour_ordinary_ambient_centralizers_of_odd
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc hmOdd
    (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm (Or.inl hc))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

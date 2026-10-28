module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.FourCompletion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryCompletion.FourRecognition

/-!
# The chosen-module unitary-four exit on the constructed carrier

At W = wholeReduced T L, construct the full-normalizer extension from the
original prepared row and apply the accepted recognition and GlobalExit APIs.
Only the ambient bound on this exact extension remains. Both orientations,
the degree-two comparison, and q = 4 are retained; the unitary exponent is m.

Source: Aschbacher–Smith 5.3.1–4, F.4.24 and Chapter12, pp.658–659,287,795.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
open ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- A named chosen-module instance of the same prepared extension construction. -/
def rankOne_unitaryFourNormalizerMarking (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm) :
    Global.UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm :=
  d.unitaryFourNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc

/-- Eliminate the extension and compatibility inputs at the literal whole reduced module. -/
theorem rankOne_unitaryFour_constructed_recognition (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
    (horder : Nat.card G ≤ Nat.card
      (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc).extension.carrier) :
    1 < m ∧ n = 2*m ∧ Nat.card G = Nat.card
      (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc).extension.carrier ∧
      ClassicalGroup.IsPSU G 4 (2^m) :=
  d.unitaryFour_constructed_recognition (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m hm hc horder

/-- Close the original U₄ row using only the same-carrier ambient order bound. -/
theorem rankOne_globalExit_of_unitaryFour_constructed (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
    (horder : Nat.card G ≤ Nat.card
      (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc).extension.carrier) :
    RankOneModule.GlobalExit G :=
  D.rankOne_globalExit_of_unitary_extension h hmany hn hpsl hH d hp m hm hc
    (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc).extension
    (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc).full_comparison horder

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

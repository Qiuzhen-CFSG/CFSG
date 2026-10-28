module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Recognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four

/-!
# Original chosen-module U₄ source and GlobalExit

The whole reduced module supplies the original full KnownSimple input. The
prepared source producer now proves innerness of the original Sylow, applies
the ambient two-class order comparison on its actual full-normalizer
extension, and feeds that same marked extension to the existing completion
recognizer. The literal output is PSU₄(2^m), with m > 1 and original exponent
n = 2*m, for either comparison orientation and q = 4.

Source: Aschbacher–Smith 5.3.2–4, F.4.35–43, and Chapter 12, printed
pp.658–659, 292–296, and795 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion
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
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
include D h hmany hn hpsl hH d hp hc

/-- The actual full-normalizer extension and both original endpoint markings,
with the ambient order comparison discharged. -/
theorem rankOne_unitaryFour_source :
    ∃ E : FourExtension m hm, Compatible L (residual H) E ∧
      Nat.card G ≤ Nat.card E.carrier := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFour_source hi hH hp m hm hc

/-- The original Chapter 12 completion input, including exact whole overlap
and the two native coset-cardinality bounds. -/
theorem rankOne_unitaryFour_completion :
    let E := (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc).extension
    1 < m ∧ n = 2*m ∧
      ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
          (G := NormalizerJoin L (residual H)),
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Nat.card (NormalizerJoin L (residual H)) ≤ Nat.card E.carrier ∧
        ∀ i : Bool, Nat.card (NormalizerJoin L (residual H) ⧸ c.cosetFamily i) ≤
          Nat.card (ProjectiveGroup m hm ⧸ SourceExtension.nativeFamily
            (P₀ := pointParabolic m hm) (P₁ := planeParabolic m hm) i) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFour_completion hi hH hp m hm hc

/-- Unconditional recognition of the original prepared U₄ row, at exponent
m and with the actual order equality on the constructed carrier. -/
theorem rankOne_unitaryFour_recognition :
    1 < m ∧ n = 2*m ∧ Nat.card G = Nat.card
      (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc).extension.carrier ∧
      ClassicalGroup.IsPSU G 4 (2^m) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFour_recognition hi hH hp m hm hc

/-- The actual source branch produces the required rank-one global exit. -/
theorem rankOne_globalExit_of_unitaryFour : RankOneModule.GlobalExit G := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  have hs := d.unitaryFour_sylow_eq_inner hi hH hp m hm hc
  have horder := d.unitaryFour_order_of_inner_sylow hi hH hp m hm hc hs
    (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc)
  exact D.rankOne_globalExit_of_unitaryFour_constructed h hmany hn hpsl hH d hp m hm hc horder.le

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

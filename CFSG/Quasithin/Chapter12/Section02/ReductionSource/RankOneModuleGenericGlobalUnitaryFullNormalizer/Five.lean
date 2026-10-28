module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.FiveCompletion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryCompletion

/-!
# The chosen-module unitary-five extension and completion

At the literal whole-reduced module, the original prepared comparison
constructs the full-normalizer extension in either orientation. The existing
completion theorem then needs only the ambient order bound on this same
carrier. The full common normalizer and projective kernel are retained.

Source: Aschbacher–Smith 5.3.1–2, F.4.24 and Chapter12,
printed pp.658–659,287,795. Final U₅ recognition and the ambient order proof
are separate obligations.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
open ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The constructed extension at W = wholeReduced T L. -/
def rankOne_unitaryFiveNormalizerMarking (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam.reverse)) :
    Global.UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U :=
  d.unitaryFiveNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc

/-- Apply the existing literal completion to the extension produced by the
original input, with no extension or compatibility premise remaining. -/
theorem rankOne_unitaryFive_constructed_completion (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam.reverse))
    (horder : Nat.card G ≤ Nat.card
      (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc).extension.carrier) :
    let E := (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc).extension
    ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
        (G := NormalizerJoin L (residual H)),
      c.left.range ⊓ c.right.range = c.middle.range ∧
      Nat.card (NormalizerJoin L (residual H)) ≤ Nat.card E.carrier :=
  rankOne_unitaryFive_completion_input U
    (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc).extension
    (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc).full_comparison horder

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

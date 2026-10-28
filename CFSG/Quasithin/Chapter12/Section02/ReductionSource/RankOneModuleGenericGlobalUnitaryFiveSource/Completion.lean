module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Completion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryCompletion.FiveRecognition

/-!
# The U₅ source order and recognition in the original Chapter 12 row

The chosen module supplies the original whole-reduced input and its actual
full-normalizer marking. Both F.4.42 quotients and F.4.43 discharge the
ambient order premise for that same extension. Its literal completion and
the existing recognition theorem give PSU₅(4) and the unitary exponent-two
GlobalExit, with no extra actor, centralizer or order hypothesis.

Source: Aschbacher–Smith 12.2.22, 5.3.1–4 and F.4.42–44,
printed pp.795,658–659,295–296 of refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The same selected marked extension has the ambient order and literal
normalizer completion, with every source premise discharged. -/
theorem rankOne_unitaryFive_source_completion
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
    Nat.card G = Nat.card r.extension.carrier ∧
    ∃ c : RankTwoAmalgam.FaithfulCompletion r.extension.amalgam
        (G := NormalizerJoin L (residual H)),
      c.left.range ⊓ c.right.range = c.middle.range ∧
      Nat.card (NormalizerJoin L (residual H)) ≤ Nat.card r.extension.carrier := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
  have ho := d.unitaryFive_source_card_eq hi hH hp U hc r
  exact ⟨ho,rankOne_unitaryFive_completion_input U r.extension r.full_comparison ho.le⟩

/-- The original Chapter 12 U₅ row recognizes the ambient group itself. -/
theorem rankOne_unitaryFive_source_recognition
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
    n = 4 ∧ Nat.card G = Nat.card r.extension.carrier ∧ ClassicalGroup.IsPSU G 5 4 := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
  exact d.unitaryFive_source_recognition hi hH hp U hc r

/-- The proved U₅ source branch closes the actual unitary-five GlobalExit. -/
theorem rankOne_globalExit_of_unitaryFive_source
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
    RankOneModule.GlobalExit G := by
  obtain ⟨_,_,hpsu⟩ := D.rankOne_unitaryFive_source_recognition h hmany hn hpsl hH d hp U hc
  exact Or.inl ⟨2,by decide,ClassificationModels.IsRankTwoModel.unitary_five rfl hpsu⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

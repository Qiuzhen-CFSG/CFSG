module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Completion

/-!
# Unconditional prepared U₅ source input

Construct the actual full-normalizer marking before applying the U₅ ambient
source proof. The F.4.43 order equality and the literal completion refer to
this same extension. Completion recognition then gives PSU₅(4), retaining
the projective kernel of order five, both comparison orientations, and the
original rank-one exponent four. No realization, actor or order premise is
left to the caller.

Source: Aschbacher–Smith 5.3.1–4 and F.4.42–44, printed pp.658–659,295–296
of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
include d h hH hp hc

/-- The prepared comparison constructs the full-normalizer extension and
proves its ambient order bound on that same marked extension. -/
theorem Preparation.unitaryFive_source :
    ∃ E : FiveExtension U, Compatible L (residual H) E ∧
      Nat.card G ≤ Nat.card E.carrier := by
  let r := d.unitaryFiveNormalizerMarking h hH hp U hc
  exact ⟨r.extension,r.full_comparison,(d.unitaryFive_source_card_eq h hH hp U hc r).le⟩

/-- The constructed marking supplies the original normalizer completion
with exact whole overlap and the proved order of that same carrier. -/
theorem Preparation.unitaryFive_completion :
    let E := (d.unitaryFiveNormalizerMarking h hH hp U hc).extension
    Nat.card G = Nat.card E.carrier ∧
    ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
        (G := NormalizerJoin L (residual H)),
      c.left.range ⊓ c.right.range = c.middle.range ∧
      Nat.card (NormalizerJoin L (residual H)) ≤ Nat.card E.carrier :=
  d.unitaryFive_source_completion h hH hp U hc (d.unitaryFiveNormalizerMarking h hH hp U hc)

/-- The prepared U₅ row recognizes the ambient group itself without a
supplied marking, extension or order bound. The unitary parameter is four. -/
theorem Preparation.unitaryFive_recognition :
    n = 4 ∧ Nat.card G = Nat.card
      (d.unitaryFiveNormalizerMarking h hH hp U hc).extension.carrier ∧
      ClassicalGroup.IsPSU G 5 4 :=
  d.unitaryFive_source_recognition h hH hp U hc (d.unitaryFiveNormalizerMarking h hH hp U hc)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

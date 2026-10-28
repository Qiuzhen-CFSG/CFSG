module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion

/-!
# The unitary-five completion on the constructed extension

The original prepared row supplies the marked full-normalizer extension.
Apply the existing completion to that exact carrier, removing both the
extension and compatible-isomorphism premises. The remaining ambient order
bound refers to the same named extension used in the marking.

Source: Aschbacher–Smith 5.3.2 and F.4.24, printed pp.659 and 287.
This construction does not discharge the independent F.4.43 ambient order
comparison or the final arbitrary-extension recognition obligation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The faithful completion retains the whole original overlap and the full
extension order bound on the actual constructed carrier. -/
theorem Preparation.unitaryFive_constructed_completion
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (horder : Nat.card G ≤ Nat.card
      (d.unitaryFiveNormalizerMarking h hH hp U hc).extension.carrier) :
    let E := (d.unitaryFiveNormalizerMarking h hH hp U hc).extension
    ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
        (G := NormalizerJoin L (residual H)),
      c.left.range ⊓ c.right.range = c.middle.range ∧
      Nat.card (NormalizerJoin L (residual H)) ≤ Nat.card E.carrier :=
  five_normalizer_completion L H U
    (d.unitaryFiveNormalizerMarking h hH hp U hc).extension
    (d.unitaryFiveNormalizerMarking h hH hp U hc).full_comparison horder

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

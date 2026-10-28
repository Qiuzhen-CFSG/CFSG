module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Order
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.FiveRecognition

/-!
# Completion and recognition from the proved U₅ ambient order

The two full involution-centralizer comparisons give the order of the same
marked extension, before invoking completion recognition. The literal
normalizer-pair completion therefore satisfies its order bound and retains
its whole overlap. The existing recognition theorem then identifies the
original simple group as PSU₅(4), preserving the original rank-one exponent.

Source: Aschbacher–Smith F.4.24, F.4.43–44 and 5.3.1–4,
printed pp.287,296,658–659 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The original normalizer pair completes this exact marked extension,
with its order bound discharged by the ambient source proof. -/
theorem Preparation.unitaryFive_source_completion
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
 :
    Nat.card G = Nat.card r.extension.carrier ∧
    ∃ c : RankTwoAmalgam.FaithfulCompletion r.extension.amalgam
        (G := NormalizerJoin L (residual H)),
      c.left.range ⊓ c.right.range = c.middle.range ∧
      Nat.card (NormalizerJoin L (residual H)) ≤ Nat.card r.extension.carrier := by
  have ho := d.unitaryFive_source_card_eq h hH hp U hc r
  exact ⟨ho,five_normalizer_completion L H U r.extension r.full_comparison ho.le⟩

/-- Recognition consumes the proved order of the same marked extension;
no ambient order or centralizer premise remains. -/
theorem Preparation.unitaryFive_source_recognition
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
 :
    n = 4 ∧ Nat.card G = Nat.card r.extension.carrier ∧ ClassicalGroup.IsPSU G 5 4 :=
  d.unitaryFive_extension_recognition h hH hp U hc r.extension r.full_comparison
    (d.unitaryFive_source_card_eq h hH hp U hc r).le

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

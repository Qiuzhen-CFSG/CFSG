module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.FourRecognition

/-!
# Completion and recognition on the constructed unitary-four carrier

The prepared row fixes the genuine full-normalizer extension. Applying the
existing completion and recognition theorems to that same extension removes
the extension and compatible-isomorphism premises. Only the ambient order
bound remains, on precisely the constructed carrier.

Source: Aschbacher–Smith 5.3.2–4 and F.4.24, printed pp.659 and287.
The unconditional F.4.43 ambient order argument is a separate obligation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The literal completion of the constructed full extension. -/
theorem Preparation.unitaryFour_constructed_completion
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (horder : Nat.card G ≤ Nat.card
      (d.unitaryFourNormalizerMarking h hH hp m hm hc).extension.carrier) :
    let E := (d.unitaryFourNormalizerMarking h hH hp m hm hc).extension
    1 < m ∧ n = 2*m ∧
      ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
          (G := NormalizerJoin L (residual H)),
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Nat.card (NormalizerJoin L (residual H)) ≤ Nat.card E.carrier ∧
        ∀ i : Bool, Nat.card (NormalizerJoin L (residual H) ⧸ c.cosetFamily i) ≤
          Nat.card (ProjectiveGroup m hm ⧸ SourceExtension.nativeFamily
            (P₀ := pointParabolic m hm) (P₁ := planeParabolic m hm) i) :=
  d.unitary_completion_input h hH hp m hm hc
    (d.unitaryFourNormalizerMarking h hH hp m hm hc).extension
    (d.unitaryFourNormalizerMarking h hH hp m hm hc).full_comparison horder

/-- Original-row recognition retains only the order bound on the chosen carrier. -/
theorem Preparation.unitaryFour_constructed_recognition
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (horder : Nat.card G ≤ Nat.card
      (d.unitaryFourNormalizerMarking h hH hp m hm hc).extension.carrier) :
    1 < m ∧ n = 2*m ∧ Nat.card G = Nat.card
      (d.unitaryFourNormalizerMarking h hH hp m hm hc).extension.carrier ∧
      ClassicalGroup.IsPSU G 4 (2^m) :=
  d.unitary_extension_recognition h hH hp m hm hc
    (d.unitaryFourNormalizerMarking h hH hp m hm hc).extension
    (d.unitaryFourNormalizerMarking h hH hp m hm hc).full_comparison horder

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

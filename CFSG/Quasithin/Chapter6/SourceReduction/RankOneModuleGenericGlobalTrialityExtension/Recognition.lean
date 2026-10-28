module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtension.FullNormalizer
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.Recognition
public import CFSG.Quasithin.ClassificationModels.RankTwo

/-!
# Recognition from the constructed triality normalizer extension

The given pure comparison determines one full-normalizer marking. Applying
the accepted extension recognizer to this constructed object leaves only
the ambient order inequality on its very same carrier.

Source: Aschbacher–Smith 5.3.2–4 and F.4.24, pp.659,287–288.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
open ChapterF.SourceCompletion.TrialityNonbinary
variable {G : Type*} [Group G] [Finite G]

/-- Recognition at the original exponent from the genuine source extension,
compatible whole-normalizer marking and full ambient order bound. -/
theorem Preparation.triality_prepared_extension_recognition_of_order
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (nativeAmalgam m hm).reverse)
    (horder : Nat.card G ≤ Nat.card
      (d.trialityNormalizerMarking h hH hp m hm e).extension.carrier) :
    let E := (d.trialityNormalizerMarking h hH hp m hm e).extension
    m=n ∧ 1<m ∧
      normalizer (L : Set G) ⊔ normalizer (residual H : Set G)=⊤ ∧
      Nat.card G=Nat.card E.carrier ∧
      Nonempty (G ≃* _root_.Triality.Standard.BinaryCarrier m hm) ∧
      ClassificationModels.IsRankTwoModel G n :=
  d.triality_extension_recognition h hH hp m hm (Or.inr ⟨e⟩)
    (d.trialityNormalizerMarking h hH hp m hm e).extension
    (Or.inr ⟨(d.trialityNormalizerMarking h hH hp m hm e).comparison⟩) horder

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

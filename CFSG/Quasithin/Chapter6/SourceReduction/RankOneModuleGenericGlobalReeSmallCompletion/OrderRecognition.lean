module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeSmallCompletion.Recognition
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension.OrderRecognition

/-!
# Recognition from the original full normalizer order bound

The original source comparison gives the positive native parameter. The
full extension bound also bounds the join of the two original normalizers.
Its actual compatible completion now supplies the marked Weyl relation
unconditionally, so the existing original-normalizer assembly identifies G
with the native Ree group. Only the source owner's extension, compatible
whole diagram and ambient full order bound remain as inputs.

Source: Aschbacher–Smith 5.3.1–4 and F.4.24, pp.658–659,287–288.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
open ChapterF.SourceCompletion.GeneralReeExtension
variable {G : Type*} [Group G] [Finite G]

/-- The literal original-normalizer application, with no additional Weyl,
fixed-neighbor, diameter or group-recognition premise. -/
theorem Preparation.ree_full_normalizers_recognition_of_order_bound
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
    (E : SourceExtension m) (e : ReeSmallCompletion.NormalizerComparison L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    2*m+1 = n ∧ 0 < m ∧
      normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
      Nat.card G = Nat.card E.carrier ∧ Nonempty (G ≃* ReeF4.Model m) := by
  have hm : 0 < m := by
    rcases he with he | he
    · exact (d.not_ree_unreversed h hH.1.1.2 hp m he).elim
    · obtain ⟨f⟩ := he
      exact (d.ree_local_structure h hH.1.1.2 hp m f).2.1
  have hX : Nat.card (normalizer (L : Set G) ⊔ normalizer (residual H : Set G) : Subgroup G)
      ≤ Nat.card E.carrier :=
    (Nat.card_le_card_of_injective _ (normalizer (L : Set G) ⊔
      normalizer (residual H : Set G)).subtype_injective).trans horder
  exact d.ree_full_normalizers_recognition_of_weyl_relation h hH hp m he E e horder
    (weylProduct_eight_eq_one E (ReeSmallCompletion.normalizerCompletion L (residual H) E e)
      hm (ReeSmallCompletion.normalizerCompletion_overlap L (residual H) E e) hX)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

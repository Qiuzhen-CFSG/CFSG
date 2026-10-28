module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialitySmallCompletion
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.Recognition
public import CFSG.Quasithin.ClassificationModels.RankTwo

/-!
# Recognizing the original full-normalizer triality row

The source comparison excludes the wrong orientation and fixes m=n>1.
The full extension order bound makes the whole-normalizer join equal G.
Marked recognition of its completion and the original ambient simplicity
then identify G with the actual native triality carrier. Only the source
extension realization, compatible marking and ambient order bound remain
inputs to the parent assembly.

Source: Aschbacher--Smith 5.3.1--4 and F.4.24, pp.658--659,287--288.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
open ChapterF.SourceCompletion.TrialityNonbinary
variable {G : Type*} [Group G] [Finite G]

/-- Recognition at the original exponent from the genuine source extension,
compatible whole-normalizer marking and full ambient order bound. -/
theorem Preparation.triality_extension_recognition
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse))
    (E : SourceExtension m hm)
    (hext : Nonempty (RankTwoAmalgam.Iso
        (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (residual H : Set G))) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (residual H : Set G))) E.amalgam.reverse))
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    m=n ∧ 1<m ∧
      normalizer (L : Set G) ⊔ normalizer (residual H : Set G)=⊤ ∧
      Nat.card G=Nat.card E.carrier ∧
      Nonempty (G ≃* _root_.Triality.Standard.BinaryCarrier m hm) ∧
      ClassificationModels.IsRankTwoModel G n := by
  obtain ⟨hmn,hm2,hgen,hcard,c,ho,_⟩ :=
    d.triality_full_normalizers_small_completion h hH hp m hm he E hext horder
  let X := normalizer (L : Set G) ⊔ normalizer (residual H : Set G)
  let z : X ≃* G := MulEquiv.ofBijective X.subtype
    ⟨X.subtype_injective,by
      intro g
      exact ⟨⟨g,by change g ∈ normalizer (L : Set G) ⊔ normalizer (residual H : Set G); rw [hgen]; exact mem_top g⟩,rfl⟩⟩
  let : IsSimpleGroup G := h.qtke.simple
  let : IsSimpleGroup X := z.isSimpleGroup
  obtain ⟨f⟩ := nonempty_native_mulEquiv_of_simple_of_card_le E c hm2 ho
    ((Nat.card_le_card_of_injective _ X.subtype_injective).trans horder)
  let a := z.symm.trans f
  refine ⟨hmn,hm2,hgen,hcard,⟨a⟩,?_⟩
  apply ClassificationModels.IsRankTwoModel.triality (by omega)
  have ht := (_root_.Triality.Standard.isTrialityGroupAt_carrier
    (_root_.Triality.Standard.binaryParameters m hm)).of_mulEquiv a
  simpa only [_root_.Triality.Standard.binaryParameters_q,hmn] using ht

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

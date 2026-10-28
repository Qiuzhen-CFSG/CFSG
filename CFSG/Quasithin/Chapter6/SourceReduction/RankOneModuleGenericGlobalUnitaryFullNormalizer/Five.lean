module
public import CFSG.Quasithin.Chapter5.Section03UnitaryFullNormalizer.Endpoint
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.FiveInner
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.Local

/-!
# Exact full-normalizer realization of the prepared unitary-five pair

The faithful native lift glues across the two actual local products. Both
orientations retain the same reduced comparison and the same lift on every
element of the whole common normalizer. The extension is the join of the
native inner group and that lifted image; its whole middle is exactly the
lifted image. No ambient order comparison is used.

Source: Aschbacher–Smith 5.3.1–2 and F.4.3, printed pp.658–659 and 274.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion

variable {G : Type*} [Group G]

namespace UnitaryFullNormalizer
variable {L K S : Subgroup G} {U : ChapterF.GreenBook.UnitaryFive.Model 4}

/-- Literal endpoint and whole-common-normalizer markings of the specified lift. -/
def FiveRealizes
    (left_le : ChapterF.Source.parabolic ![L,K] S 0 ≤ normalizer (L : Set G))
    (right_le : ChapterF.Source.parabolic ![L,K] S 1 ≤ normalizer (K : Set G))
    (a : UnitarySource.MarkedMiddleAction L K S U.amalgam)
    (f : UnitaryNativeLift.Five.Lift U a) (extension : FiveExtension U) : Prop :=
    ∃ F : RankTwoAmalgam.Iso (normalizerDiagram L K) extension.amalgam,
      (∀ x, (F.left (inclusion left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (f.action z).val) ∧
      extension.carrier = inner U.Carrier ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      extension.left = U.leftParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      extension.right = U.rightParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      extension.middle = ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range

/-- Literal endpoint and whole-common-normalizer markings of the specified lift. -/
def FiveRealizesReverse
    (left_le : ChapterF.Source.parabolic ![L,K] S 0 ≤ normalizer (L : Set G))
    (right_le : ChapterF.Source.parabolic ![L,K] S 1 ≤ normalizer (K : Set G))
    (a : UnitarySource.MarkedMiddleAction L K S U.amalgam.reverse)
    (f : UnitaryNativeLift.Five.LiftReverse U a) (extension : FiveExtension U) : Prop :=
    ∃ F : RankTwoAmalgam.Iso (normalizerDiagram L K) extension.amalgam.reverse,
      (∀ x, (F.left (inclusion left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (f.action z).val) ∧
      extension.carrier = inner U.Carrier ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      extension.left = U.leftParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      extension.right = U.rightParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      extension.middle = ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range

end UnitaryFullNormalizer

/-- Exact realization data for a specified native comparison and lift. -/
structure UnitaryFiveNormalizerMarking (L K S : Subgroup G) (U : ChapterF.GreenBook.UnitaryFive.Model 4) where
  extension : FiveExtension U
  left_le : ChapterF.Source.parabolic ![L,K] S 0 ≤ normalizer (L : Set G)
  right_le : ChapterF.Source.parabolic ![L,K] S 1 ≤ normalizer (K : Set G)
  marking :
    (∃ a : UnitarySource.MarkedMiddleAction L K S U.amalgam,
      ∃ f : UnitaryNativeLift.Five.Lift U a,
      UnitaryFullNormalizer.FiveRealizes left_le right_le a f extension) ∨
    (∃ a : UnitarySource.MarkedMiddleAction L K S U.amalgam.reverse,
      ∃ f : UnitaryNativeLift.Five.LiftReverse U a,
      UnitaryFullNormalizer.FiveRealizesReverse left_le right_le a f extension)

/-- Forgetting only the extra marking supplies the existing completion input. -/
theorem UnitaryFiveNormalizerMarking.full_comparison
    {L K S : Subgroup G} {U : ChapterF.GreenBook.UnitaryFive.Model 4}
    (a : UnitaryFiveNormalizerMarking L K S U) : Compatible L K a.extension := by
  rcases a.marking with ⟨_,_,F,_⟩ | ⟨_,_,F,_⟩
  · exact Or.inl ⟨F⟩
  · exact Or.inr ⟨F⟩

namespace UnitaryFullNormalizer

private theorem five_conjugation_transport {B : Type*} [Group B]
    (P : Subgroup G) (R : Subgroup B) (e : P ≃* R)
    (a : MulAut R) (f : MulAut B) (d : G)
    (hc : ∀ x, (e.symm (a x)).val = d * (e.symm x).val * d⁻¹)
    (hf : ∀ x : R, f x.val = (a x).val) (x : P) :
    ∃ hx : d*x.val*d⁻¹ ∈ P, (e ⟨d*x.val*d⁻¹,hx⟩).val = f (e x).val := by
  have hh := hc (e x)
  rw [e.symm_apply_apply] at hh
  refine ⟨hh ▸ (e.symm (a (e x))).property, ?_⟩
  have he : (⟨d*x.val*d⁻¹,hh ▸ (e.symm (a (e x))).property⟩ : P) =
      e.symm (a (e x)) := Subtype.ext hh.symm
  rw [he,e.apply_symm_apply,hf]

end UnitaryFullNormalizer

variable [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- Realize any supplied coherent lift, retaining its exact action and comparison. -/
theorem Preparation.unitaryFive_realizes_lift
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
      U.amalgam) (f : UnitaryNativeLift.Five.Lift U a) :
    ∃ hleft : ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 ≤ normalizer (L : Set G),
    ∃ hright : ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1 ≤ normalizer (residual H : Set G),
    ∃ E : FiveExtension U, UnitaryFullNormalizer.FiveRealizes hleft hright a f E := by
  have hl := d.unitaryFive_normalizer_local_conditions h hH hp U hc
  have cc : ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) :=
    .unitaryFive U hc
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L)
  let M₀ := normalizer (L : Set G)
  let M₁ := normalizer (residual H : Set G)
  let D := M₀ ⊓ M₁
  let B₀ := P 0 ⊓ P 1

  obtain ⟨hPM,hPD,hprod₀,hprod₁⟩ := d.reduced_normalizer_endpoint_data h hH hp cc hl a.middle_le
  have hact₀ := fun g => UnitaryFullNormalizer.five_conjugation_transport (P 0) U.leftParabolic
    a.comparison.left (a.action g).left (f.action g).val g.val (a.left_conjugation g)
    (UnitaryNativeLift.Five.left f g)
  have hact₁ := fun g => UnitaryFullNormalizer.five_conjugation_transport (P 1) U.rightParabolic
    a.comparison.right (a.action g).right (f.action g).val g.val (a.right_conjugation g)
    (UnitaryNativeLift.Five.right f g)
  obtain ⟨E,F,hF₀,hF₁,hFD,hE,hE₀,hE₁,hED⟩ :=
    Chapter5.Section03UnitaryFullNormalizer.extension_of_native_lift
      U.leftParabolic U.rightParabolic U.overlap rfl
      (Chapter5.UnitaryNativeLift.Five.parabolics_generate U) (five_conj_injective U)
      (P 0) (P 1) M₀ M₁ D B₀ (hPM 0) (hPM 1) inf_le_left inf_le_right a.middle_le
      (hPD 0) (hPD 1) hprod₀ hprod₁ a.comparison.left a.comparison.right a.comparison.middle
      (fun b => congrArg Subtype.val (a.comparison.left_commutes b))
      (fun b => congrArg Subtype.val (a.comparison.right_commutes b))
      f.action f.faithful (UnitaryFullNormalizer.five_inner_preimage f)
      (fun b => congrArg Subtype.val (UnitaryNativeLift.Five.inner_action f b)) hact₀ hact₁
  exact ⟨hPM 0,hPM 1,E,F,hF₀,hF₁,hFD,hE,hE₀,hE₁,hED⟩

/-- Realize any supplied coherent lift, retaining its exact action and comparison. -/
theorem Preparation.unitaryFive_realizes_lift_reverse
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
      U.amalgam.reverse) (f : UnitaryNativeLift.Five.LiftReverse U a) :
    ∃ hleft : ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 ≤ normalizer (L : Set G),
    ∃ hright : ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1 ≤ normalizer (residual H : Set G),
    ∃ E : FiveExtension U, UnitaryFullNormalizer.FiveRealizesReverse hleft hright a f E := by
  have hl := d.unitaryFive_normalizer_local_conditions h hH hp U hc
  have cc : ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) :=
    .unitaryFive U hc
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L)
  let M₀ := normalizer (L : Set G)
  let M₁ := normalizer (residual H : Set G)
  let D := M₀ ⊓ M₁
  let B₀ := P 0 ⊓ P 1

  obtain ⟨hPM,hPD,hprod₀,hprod₁⟩ := d.reduced_normalizer_endpoint_data h hH hp cc hl a.middle_le
  have hact₀ := fun g => UnitaryFullNormalizer.five_conjugation_transport (P 0) U.rightParabolic
    a.comparison.left (a.action g).left (f.action g).val g.val (a.left_conjugation g)
    (UnitaryNativeLift.Five.leftReverse f g)
  have hact₁ := fun g => UnitaryFullNormalizer.five_conjugation_transport (P 1) U.leftParabolic
    a.comparison.right (a.action g).right (f.action g).val g.val (a.right_conjugation g)
    (UnitaryNativeLift.Five.rightReverse f g)
  obtain ⟨E,F,hF₁,hF₀,hFD,hE,hE₀,hE₁,hED⟩ :=
    Chapter5.Section03UnitaryFullNormalizer.extension_of_native_lift
      U.leftParabolic U.rightParabolic U.overlap rfl
      (Chapter5.UnitaryNativeLift.Five.parabolics_generate U) (five_conj_injective U)
      (P 1) (P 0) M₁ M₀ D B₀ (hPM 1) (hPM 0) inf_le_right inf_le_left a.middle_le
      (hPD 1) (hPD 0) hprod₁ hprod₀ a.comparison.right a.comparison.left a.comparison.middle
      (fun b => congrArg Subtype.val (a.comparison.right_commutes b))
      (fun b => congrArg Subtype.val (a.comparison.left_commutes b))
      f.action f.faithful (UnitaryFullNormalizer.five_inner_preimage_reverse f)
      (fun b => congrArg Subtype.val (UnitaryNativeLift.Five.inner_actionReverse f b)) hact₁ hact₀
  exact ⟨hPM 0,hPM 1,E,F.reverse,hF₀,hF₁,hFD,hE,hE₀,hE₁,hED⟩

/-- The original prepared row constructs a marked extension of both full
normalizers, in both orientations, on the projective carrier over the field of order sixteen. -/
theorem Preparation.unitaryFive_full_normalizer_marking
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    Nonempty
      (UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U) := by
  have ha := d.unitaryFive_native_lifted_middle_action h hH hp U hc
  rcases ha with ⟨a,⟨f⟩⟩ | ⟨a,⟨f⟩⟩
  · obtain ⟨hleft,hright,E,hE⟩ := d.unitaryFive_realizes_lift h hH hp U hc a f
    exact ⟨⟨E,hleft,hright,Or.inl ⟨a,f,hE⟩⟩⟩
  · obtain ⟨hleft,hright,E,hE⟩ := d.unitaryFive_realizes_lift_reverse h hH hp U hc a f
    exact ⟨⟨E,hleft,hright,Or.inr ⟨a,f,hE⟩⟩⟩

/-- Fix the realized carrier for the subsequent ambient order comparison. -/
def Preparation.unitaryFiveNormalizerMarking
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U :=
  (d.unitaryFive_full_normalizer_marking h hH hp U hc).some

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

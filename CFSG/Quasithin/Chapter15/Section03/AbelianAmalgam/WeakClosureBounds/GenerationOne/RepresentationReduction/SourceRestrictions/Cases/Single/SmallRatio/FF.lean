module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio.Models

/-!
# Natural constituents from all eleven B.4.2 cases

Apply the complete central-component catalogue comparisons separately to
all source alternatives, including the small derived groups, alternating
endpoints, central cover, and both binary-linear module rows. Only the
three natural actions survive, with their original intertwiners and the
recovered source field. The B.4.2 conclusion is an explicit earlier input.

Source: Aschbacher--Smith, B.4.2, printed p.86, used on p.1152.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
open FFExclusions.ModelRigidity

universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) {L H : Subgroup D} {f : ℕ}

theorem natural_of_full_B42 (hs : SourceModel (L ⧸ center L) f)
    (hf : 1 < f) (ho : Odd f) (hz : center L = ⊥)
    (h : IrreducibleActionCase ρ L H) : NaturalConstituent ρ L f := by
  cases h with
  | linearTwo F _ e _ _ =>
    have hc := hs.componentModel hf ho (.linearTwo F.Carrier F.degree_pos F.card_eq
      (centralQuotientCongr e.groupEquiv))
    exact .linearTwo F (F.card_eq.trans hc.2) e
  | linearThree F _ e _ =>
    have hc := hs.componentModel hf ho (.linearThree F.Carrier F.degree_pos F.card_eq
      (centralQuotientCongr e.groupEquiv))
    exact .linearThree F (F.card_eq.trans hc.2) e
  | symplectic F hn _ e _ =>
    have hc := hs.componentModel hf ho (.symplecticFour F.Carrier hn F.card_eq
      (centralQuotientCongr e.groupEquiv))
    exact .symplecticFour F (F.card_eq.trans hc.2) e
  | symplecticTwo e _ =>
    have hc := hs.componentModel hf ho (.symplecticFourTwoDerived
      ((centerQuotientEquiv hz).trans e.subgroupEquiv))
    rcases hc.1 with he | he | he <;> cases he
  | g2 F hn _ e _ _ =>
    have hc := hs.componentModel hf ho (.gTwo F.Carrier hn F.card_eq
      ((centerQuotientEquiv hz).trans e.groupEquiv))
    rcases hc.1 with he | he | he <;> cases he
  | g2Two e _ _ =>
    have hc := hs.componentModel hf ho (.gTwoTwoDerived
      ((centerQuotientEquiv hz).trans e.subgroupEquiv))
    rcases hc.1 with he | he | he <;> cases he
  | symmetric n hn e _ _ =>
    rcases hn with rfl | rfl
    · have hc := hs.componentModel hf ho (.alternatingFive
        ((centerQuotientEquiv hz).trans e.subgroupEquiv))
      rcases hc.1 with he | he | he <;> cases he
    · have hc := hs.componentModel hf ho (.alternatingSeven
        ((centerQuotientEquiv hz).trans e.subgroupEquiv))
      rcases hc.1 with he | he | he <;> cases he
  | alternatingSix _ e _ _ =>
    have hc := hs.componentModel hf ho (.alternatingSix
      ((centerQuotientEquiv hz).trans e.groupEquiv))
    rcases hc.1 with he | he | he <;> cases he
  | alternatingSeven _ _ e _ _ _ =>
    have hc := hs.componentModel hf ho (.alternatingSeven
      ((centerQuotientEquiv hz).trans e))
    rcases hc.1 with he | he | he <;> cases he
  | tripleSix _ a _ =>
    have hc := hs.componentModel hf ho (.alternatingSix a.quotientEquiv)
    rcases hc.1 with he | he | he <;> cases he
  | binaryLinear d hd _ e _ =>
    rcases hd with rfl | rfl
    · have hc := hs.componentModel hf ho (.linearFourTwo (centralQuotientCongr e.groupEquiv))
      rcases hc.1 with he | he | he <;> cases he
    · have hc := hs.componentModel hf ho (.linearFiveTwo (centralQuotientCongr e.groupEquiv))
      rcases hc.1 with he | he | he <;> cases he
  | orthogonalSix _ _ e _ _ =>
    have hc := hs.componentModel hf ho (.linearFourTwo
      (centralQuotientCongr (e.groupEquiv.trans alternatingEightLinearEquiv)))
    rcases hc.1 with he | he | he <;> cases he
  | symmetricEight _ e _ =>
    have hc := hs.componentModel hf ho (.linearFourTwo
      (centralQuotientCongr (e.subgroupEquiv.trans alternatingEightLinearEquiv)))
    rcases hc.1 with he | he | he <;> cases he
  | exteriorFive _ _ e _ _ _ =>
    have hc := hs.componentModel hf ho (.linearFiveTwo (centralQuotientCongr e))
    rcases hc.1 with he | he | he <;> cases he

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio

module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Definitions
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The two A₇ rows of the source module classification

The central quotient of the original two-core quotient has order 2520.
Its centerless nontrivial images have that same order. This excludes the
binary linear rows and restricts the alternating row to degree seven.
Divisibility alone excludes the derived G₂(2) and triple-A₆ rows.

Thus the genuine seven-case classification leaves either the natural
fixed-space quotient or the entire four-dimensional module. No central
cover is replaced by its simple quotient during this comparison.
Source: Aschbacher--Smith, Lemma 12.3.3, printed p.807, invoking 12.2.2(3).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Setup
variable (S : Setup T L V)

include S in
private theorem centralQuotient_card :
    Nat.card ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) = 2520 := by
  rw [Nat.card_congr ((centralPreimageQuotientEquiv (pCore 2 L)).symm.trans
    S.quotient).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

include S in
private theorem central_card_dvd : 2520 ∣ Nat.card (L ⧸ pCore 2 L) := by
  rw [← S.centralQuotient_card]
  exact Subgroup.card_dvd_of_surjective (QuotientGroup.mk' (center (L ⧸ pCore 2 L)))
    (QuotientGroup.mk'_surjective _)

include S in
private theorem card_centerless_image
    {A : Type*} [Group A] [Nontrivial A]
    (f : (L ⧸ pCore 2 L) →* A) (hf : Function.Surjective f)
    (hz : center A = ⊥) : Nat.card A = 2520 := by
  let := S.hypothesis.quasisimple
  let e := (IsQuasisimple.centralQuotientEquiv f hf).trans
    ((QuotientGroup.quotientMulEquivOfEq hz).trans (QuotientGroup.quotientBot (G := A)))
  rw [← Nat.card_congr e.toEquiv]
  exact S.centralQuotient_card

private theorem linear_card (n : ℕ) :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) =
      ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  let e := MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective,
      BinaryLinear.OuterCyclic.binary_toGL_surjective n⟩
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  rfl

include S in
private theorem not_linear {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 5)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False := by
  let := S.hypothesis.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) :=
    S.hypothesis.quasisimple.simple
  let : Nontrivial (L ⧸ pCore 2 L) :=
    (QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L))).nontrivial
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := e.injective.nontrivial
  have hc := S.card_centerless_image e.toMonoidHom e.surjective
    (BinaryLinear.OuterCyclic.binary_center_eq_bot (by rcases hn with rfl | rfl | rfl <;> decide))
  rw [linear_card] at hc
  rcases hn with rfl | rfl | rfl <;> norm_num [Fin.prod_univ_succ] at hc

/-- The seven printed alternatives reduce to precisely the two cases used in
12.3.3, on the original chosen module and faithful actor. -/
theorem natural_quotient_or_four (rows : ModuleAlternatives1222 S.chosen) :
    (letI := S.chosen.actionCentralizer_normal;
      Nonempty (ActionEquiv S.chosen.faithfulCentralAction (alternatingNatural 7))) ∨
    (letI := S.chosen.actionCentralizer_normal;
      Nonempty ((L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃*
        alternatingGroup (Fin 7)) ∧ Module.finrank (ZMod 2) S.chosen.space = 4) := by
  cases rows with
  | linear n hn a => exact (S.not_linear hn a.groupEquiv).elim
  | linearThreeExtension e _ _ => exact (S.not_linear (Or.inl rfl) e).elim
  | linearFiveExterior e _ _ => exact (S.not_linear (Or.inr (Or.inr rfl)) e).elim
  | alternating n hlo hhi a =>
    let := S.chosen.actionCentralizer_normal
    let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    let : Nontrivial (alternatingGroup (Fin n)) := by
      let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa)
      infer_instance
    have hc := S.card_centerless_image
      (a.groupEquiv.toMonoidHom.comp S.chosen.coreToFaithful)
      (a.groupEquiv.surjective.comp S.chosen.coreToFaithful_surjective)
      (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega)))
    have hn : n = 7 := by
      rw [nat_card_alternatingGroup, Nat.card_fin] at hc
      have hcases : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
      rcases hcases with rfl | rfl | rfl | rfl
      · norm_num [Nat.factorial] at hc
      · norm_num [Nat.factorial] at hc
      · rfl
      · norm_num [Nat.factorial] at hc
    subst n
    exact Or.inl ⟨a⟩
  | alternatingSevenFour e hd => exact Or.inr ⟨⟨e⟩,hd⟩
  | g2 a =>
    have hc := S.central_card_dvd
    rw [Nat.card_congr a.groupEquiv.toEquiv,
      Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hc
    norm_num at hc
  | tripleSix e _ _ _ =>
    have hc := S.central_card_dvd
    rw [Nat.card_congr e.toEquiv, Atlas.Codes.hexEven_card] at hc
    norm_num at hc

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

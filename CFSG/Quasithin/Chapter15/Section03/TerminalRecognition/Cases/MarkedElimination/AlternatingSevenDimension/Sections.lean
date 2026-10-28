module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.MarkedElimination.AlternatingSevenDimension.Orders
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Removing the central quotient in the A₇ module case

B.5.1(2) forces splitting for A₇, since none of its nonsplit actors has
order 2520. Its irreducible list then has only the four-dimensional A₇
case. When the original module is fully moved and the component is the
whole actor, the moved section is the whole space and its central kernel
is zero. Thus the dimension belongs to the original module.

Source: Aschbacher–Smith, B.4.2(7), B.5.1(1),(2), printed pp.86 and 99.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.MarkedElimination.AlternatingSevenDimension

variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]

private theorem alt_card_ne {n : ℕ} (hn : n = 6 ∨ n = 8) :
    Nat.card (alternatingGroup (Fin n)) ≠ 2520 := by
  rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] <;>
    norm_num [Nat.factorial]

private theorem eq_card_of_equiv {A B : Type*} [Group A] [Group B]
    (h : Nat.card A = 2520) (e : A ≃* B) : Nat.card B = 2520 :=
  (Nat.card_congr e.toEquiv).symm.trans h

omit [Finite D] in
theorem not_nonsplit_natural (ρ : Representation (ZMod 2) D W)
    (hD : Nat.card D = 2520) : ¬ NonsplitNatural ρ := by
  intro h
  cases h with
  | linearTwo F h => exact not_sl_two F (eq_card_of_equiv hD h.some.groupEquiv)
  | symplectic F h => exact not_sp_four F (eq_card_of_equiv hD h.some.groupEquiv)
  | g2 F h => exact not_g2 F (eq_card_of_equiv hD h.some.groupEquiv)
  | alternatingSix h => exact alt_card_ne (Or.inl rfl) (eq_card_of_equiv hD h.some.groupEquiv)
  | alternatingEight h => exact alt_card_ne (Or.inr rfl) (eq_card_of_equiv hD h.some.groupEquiv)
  | derivedG2 h => exact not_g2_derived (eq_card_of_equiv hD h.some.groupEquiv)
  | linearThree h => exact not_sl_three BinaryField.two (eq_card_of_equiv hD h.some.groupEquiv)

private theorem not_binary_linear {A : Type*} [Group A] (hA : Nat.card A = 2520)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : A ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False := by
  rcases hn with rfl | rfl
  · exact not_sl_four (eq_card_of_equiv hA e)
  · exact not_sl_five (eq_card_of_equiv hA e)

theorem irreducible_dimension (ρ : Representation (ZMod 2) D W)
    {L J : Subgroup D} (hD : Nat.card D = 2520) (hL : Nat.card L = 2520)
    (h : IrreducibleActionCase ρ L J) : Module.finrank (ZMod 2) W = 4 := by
  cases h with
  | linearTwo F _ e _ _ => exact (not_sl_two F (eq_card_of_equiv hL e.groupEquiv)).elim
  | linearThree F _ e _ => exact (not_sl_three F (eq_card_of_equiv hL e.groupEquiv)).elim
  | symplectic F _ _ e _ => exact (not_sp_four F (eq_card_of_equiv hL e.groupEquiv)).elim
  | symplecticTwo e _ =>
    exact (alt_card_ne (Or.inl rfl)
      (eq_card_of_equiv hL (e.subgroupEquiv.trans binarySymplecticDerivedEquiv))).elim
  | g2 F _ _ e _ _ => exact (not_g2 F (eq_card_of_equiv hL e.groupEquiv)).elim
  | g2Two e _ _ => exact (not_g2_derived (eq_card_of_equiv hL e.subgroupEquiv)).elim
  | symmetric n hn e _ _ =>
    have hc := J.card_le_card_group
    rw [Nat.card_congr e.action.groupEquiv.toEquiv, hD] at hc
    rcases hn with rfl | rfl <;>
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hc
    -- S₅ is small enough to embed, but its marked A₅ is not A₇.
    have hl := eq_card_of_equiv hL e.subgroupEquiv
    rw [nat_card_alternatingGroup] at hl
    norm_num [Nat.factorial] at hl
  | alternatingSix _ e _ _ =>
    exact (alt_card_ne (Or.inl rfl) (eq_card_of_equiv hL e.groupEquiv)).elim
  | alternatingSeven _ _ _ hd _ _ => exact hd
  | tripleSix _ a _ =>
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
    rw [hL, Nat.card_congr a.quotientEquiv.toEquiv,
      Nat.card_congr a.centerEquiv.toEquiv, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial, Nat.card_congr Multiplicative.toAdd] at hc
  | binaryLinear n hn _ e _ => exact (not_binary_linear hL hn e.groupEquiv).elim
  | orthogonalSix _ _ e _ _ =>
    exact (alt_card_ne (Or.inr rfl) (eq_card_of_equiv hL e.groupEquiv)).elim
  | symmetricEight _ e _ =>
    exact (alt_card_ne (Or.inr rfl) (eq_card_of_equiv hL e.subgroupEquiv)).elim
  | exteriorFive _ _ e _ _ _ => exact (not_sl_five (eq_card_of_equiv hL e)).elim

theorem section_dimension (ρ : Representation (ZMod 2) D W)
    {L : Subgroup D} {s : MovedSection ρ L}
    (hD : Nat.card D = 2520) (hL : Nat.card L = 2520)
    (h : QuasisimpleActionCase ρ L s) :
    Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4 := by
  cases h with
  | irreducible _ _ _ source _ => exact irreducible_dimension s.action hD hL source
  | doubleThree F _ e _ _ => exact (not_sl_three F (eq_card_of_equiv hL e.groupEquiv)).elim
  | naturalDual n hn _ e => exact (not_binary_linear hL hn e.some.groupEquiv).elim
  | repeatedNatural n r hn _ _ _ e => exact (not_binary_linear hL hn e.some.groupEquiv).elim

theorem original_dimension [Module.Finite (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {L : Subgroup D}
    (hD : Nat.card D = 2520) (hL : L = ⊤) (hm : moved ρ ⊤ = ⊤)
    (c : QuasisimpleSourceConclusion ρ L) : Module.finrank (ZMod 2) W = 4 := by
  have hLc : Nat.card L = 2520 := by
    rw [hL, Nat.card_congr Subgroup.topEquiv.toEquiv, hD]
  have hs : c.sectionData.space.toSubmodule = ⊤ := by
    rw [c.sectionData.space_eq, hL, hm]
  have hsplit : IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ L) := by
    by_contra h
    exact not_nonsplit_natural (c.sectionData.action.comp L.subtype) hLc (c.clause_two h).2
  have hfixed : fixedSpace ρ L = ⊥ := by
    simpa only [hs, top_inf_eq] using hsplit.inf_eq_bot
  have hz : c.sectionData.central.toSubmodule = ⊥ := by
    rw [c.sectionData.central_eq]
    apply le_bot_iff.mp
    intro v hv
    have hv' : (v : W) ∈ fixedSpace ρ L := fun l => congrArg Subtype.val (hv l)
    rw [hfixed] at hv'
    exact Subtype.ext hv'
  have hd := section_dimension ρ hD hLc c.clause_one
  have hr := c.sectionData.central.toSubmodule.finrank_quotient_add_finrank
  have hc0 : Module.finrank (ZMod 2) c.sectionData.central.toSubmodule = 0 := by
    rw [hz, finrank_bot]
  rw [hc0, add_zero] at hr
  rw [hr, hs, finrank_top] at hd
  exact hd

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.MarkedElimination.AlternatingSevenDimension

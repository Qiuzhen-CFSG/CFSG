module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Sections.Existence.SixOrders

/-!
# The faithful four-dimensional central section for an A₆ component

The order of the actual component eliminates the unrelated B.4.2 actions.
Each remaining possibility has binary dimension four. We use that
dimension and the source faithfulness assertion, so no symplectic-to-permutation
intertwiner is asserted or needed. The central kernel remains intact.

Source: Aschbacher–Smith, B.4.2 and B.5.1, printed pp.86 and 99, as used
in the final proof of 15.3.1, p.1155 (combined manuscript, 1 March 2004).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation.SixDimension
open SixOrders
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]

private theorem eq_card_of_equiv {A B : Type*} [Group A] [Group B]
    (h : Nat.card A = 360) (e : A ≃* B) : Nat.card B = 360 :=
  (Nat.card_congr e.toEquiv).symm.trans h

private theorem not_binary_linear {A : Type*} [Group A] (hA : Nat.card A = 360)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : A ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False := by
  rcases hn with rfl | rfl
  · exact not_sl_four (eq_card_of_equiv hA e)
  · exact not_sl_five (eq_card_of_equiv hA e)

private theorem eight_ne {A : Type*} [Group A] (hA : Nat.card A = 360)
    (e : A ≃* alternatingGroup (Fin 8)) : False := by
  have hc := eq_card_of_equiv hA e
  rw [nat_card_alternatingGroup] at hc
  norm_num [Nat.factorial] at hc

private theorem irreducible_dimension (ρ : Representation (ZMod 2) D W)
    {L J : Subgroup D} (hL : Nat.card L = 360)
    (h : IrreducibleActionCase ρ L J) : Module.finrank (ZMod 2) W = 4 := by
  cases h with
  | linearTwo F _ e _ _ => exact (not_sl_two F (eq_card_of_equiv hL e.groupEquiv)).elim
  | linearThree F _ e _ => exact (not_sl_three F (eq_card_of_equiv hL e.groupEquiv)).elim
  | symplectic F _ _ e _ => exact (not_sp_four F (eq_card_of_equiv hL e.groupEquiv)).elim
  | symplecticTwo e _ =>
    have hd := e.action.linearEquiv.finrank_eq
    simpa using hd
  | g2 F _ _ e _ _ => exact (not_g2 F (eq_card_of_equiv hL e.groupEquiv)).elim
  | g2Two e _ _ => exact (not_g2_derived (eq_card_of_equiv hL e.subgroupEquiv)).elim
  | symmetric n hn e _ _ =>
    have hc := eq_card_of_equiv hL e.subgroupEquiv
    rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] at hc <;>
      norm_num [Nat.factorial] at hc
  | alternatingSix _ e _ _ =>
    have hd := e.linearEquiv.finrank_eq
    rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide)] at hd
    simpa using hd
  | alternatingSeven _ _ _ hd _ _ => exact hd
  | tripleSix _ a _ =>
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
    rw [hL, Nat.card_congr a.quotientEquiv.toEquiv,
      Nat.card_congr a.centerEquiv.toEquiv, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial, Nat.card_congr Multiplicative.toAdd] at hc
  | binaryLinear n hn _ e _ => exact (not_binary_linear hL hn e.groupEquiv).elim
  | orthogonalSix _ _ e _ _ => exact (eight_ne hL e.groupEquiv).elim
  | symmetricEight _ e _ => exact (eight_ne hL e.subgroupEquiv).elim
  | exteriorFive _ _ e _ _ _ => exact (not_sl_five (eq_card_of_equiv hL e)).elim

/-- The A₆ component gives a faithful four-dimensional central section.
No choice of coordinates between the symplectic and permutation models is made. -/
theorem section_faithful_dimension (ρ : Representation (ZMod 2) D W)
    {L : Subgroup D} {s : MovedSection ρ L} (hL : Nat.card L = 360)
    (h : QuasisimpleActionCase ρ L s) :
    Function.Injective s.action ∧
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4 := by
  cases h with
  | irreducible _ hf _ source _ => exact ⟨hf, irreducible_dimension s.action hL source⟩
  | doubleThree F _ e _ _ => exact (not_sl_three F (eq_card_of_equiv hL e.groupEquiv)).elim
  | naturalDual n hn _ e => exact (not_binary_linear hL hn e.some.groupEquiv).elim
  | repeatedNatural n r hn _ _ _ e => exact (not_binary_linear hL hn e.some.groupEquiv).elim
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation.SixDimension

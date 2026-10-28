module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection.ActionOrders
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts

/-!
# The natural moved quotient of a binary derived G₂ component

The exact component order excludes every B.5.1 row except the marked
G₂(2) natural action. Restricting the marked action retains its literal
G₂(2)′ component. This classification is applied before any block recognition.
Source: Aschbacher–Smith B.4.2 and B.5.1, pp.86 and 99, used in 13.6.22, p.932.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection.ActionOrders
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection.Action
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

private theorem alt_card_ne {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    Nat.card (alternatingGroup (Fin n)) ≠ 6048 := by
  rcases hn with rfl | rfl | rfl | rfl <;> rw [nat_card_alternatingGroup] <;>
    norm_num [Nat.factorial]

private theorem eq_card_of_equiv {A B : Type*} [Group A] [Group B]
    (h : Nat.card A = 6048) (e : A ≃* B) : Nat.card B = 6048 :=
  (Nat.card_congr e.toEquiv).symm.trans h

private theorem not_binary_linear {A : Type*} [Group A] (hA : Nat.card A = 6048)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : A ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False := by
  rcases hn with rfl | rfl
  · exact not_sl_four (eq_card_of_equiv hA e)
  · exact not_sl_five (eq_card_of_equiv hA e)

private def derived_restriction {C H : Subgroup D}
    (e : MarkedActionEquiv ρ H C (g2Natural (ZMod 2))
      (commutator (Atlas.G2.Model (ZMod 2)))) :
    ActionEquiv (ρ.comp C.subtype) (g2DerivedNatural (ZMod 2)) where
  groupEquiv := e.subgroupEquiv
  linearEquiv := e.action.linearEquiv
  intertwines c v := by
    have h := e.action.intertwines ⟨c, e.contained c.property⟩ v
    rw [e.compatible] at h
    exact h

/-- Only the marked binary G₂ row survives the original B.4.2 list. -/
theorem irreducible_marked_rows {C H : Subgroup D}
    (eC : C ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (h : ProjectiveLine.IrreducibleActionCase ρ C H) :
    (∃ J : Subgroup D, Nonempty (MarkedActionEquiv ρ J C
      (g2Natural (ZMod 2)) (commutator (Atlas.G2.Model (ZMod 2))))) := by
  have hC : Nat.card C = 6048 := (Nat.card_congr eC.toEquiv).trans derived_g2_card
  cases h with
  | linearTwo F _ e _ _ => exact (not_sl_two F (eq_card_of_equiv hC e.groupEquiv)).elim
  | linearThree F _ e _ => exact (not_sl_three F (eq_card_of_equiv hC e.groupEquiv)).elim
  | symplectic F _ _ e _ => exact (not_sp_four F (eq_card_of_equiv hC e.groupEquiv)).elim
  | symplecticTwo e _ =>
    exact (alt_card_ne (Or.inr (Or.inl rfl))
      (eq_card_of_equiv hC (e.subgroupEquiv.trans binarySymplecticDerivedEquiv))).elim
  | g2 F _ _ e _ _ => exact (not_g2 F (eq_card_of_equiv hC e.groupEquiv)).elim
  | g2Two e _ _ => exact ⟨H, ⟨e⟩⟩
  | symmetric n hn e _ _ =>
    rcases hn with rfl | rfl
    · exact (alt_card_ne (Or.inl rfl) (eq_card_of_equiv hC e.subgroupEquiv)).elim
    · exact (alt_card_ne (Or.inr (Or.inr (Or.inl rfl))) (eq_card_of_equiv hC e.subgroupEquiv)).elim
  | alternatingSix _ e _ _ =>
    exact (alt_card_ne (Or.inr (Or.inl rfl)) (eq_card_of_equiv hC e.groupEquiv)).elim
  | alternatingSeven _ _ e _ _ _ =>
    exact (alt_card_ne (Or.inr (Or.inr (Or.inl rfl))) (eq_card_of_equiv hC e)).elim
  | tripleSix _ a _ =>
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center C)
    rw [hC, Nat.card_congr a.quotientEquiv.toEquiv,
      Nat.card_congr a.centerEquiv.toEquiv, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial, Nat.card_congr Multiplicative.toAdd] at hc
  | binaryLinear n hn _ e _ => exact (not_binary_linear hC hn e.groupEquiv).elim
  | orthogonalSix _ _ e _ _ =>
    exact (alt_card_ne (Or.inr (Or.inr (Or.inr rfl))) (eq_card_of_equiv hC e.groupEquiv)).elim
  | symmetricEight _ e _ =>
    exact (alt_card_ne (Or.inr (Or.inr (Or.inr rfl))) (eq_card_of_equiv hC e.subgroupEquiv)).elim
  | exteriorFive _ _ e _ _ _ => exact (not_sl_five (eq_card_of_equiv hC e)).elim

/-- The reducible B.5.1 rows have different component groups. The surviving
section retains its actual irreducibility, faithfulness and action coordinates. -/
theorem classification_marked_rows {C : Subgroup D}
    (eC : C ≃* commutator (Atlas.G2.Model (ZMod 2))) (s : MovedSection ρ C)
    (h : ProjectiveLine.QuasisimpleActionCase ρ C s) :
    IsIrrPlus ρ C s.space.toSubmodule ∧ Function.Injective s.action ∧
      IsIrreducible (s.action.comp C.subtype) ∧
      (∃ J : Subgroup D, Nonempty (MarkedActionEquiv s.action J C
        (g2Natural (ZMod 2)) (commutator (Atlas.G2.Model (ZMod 2))))) := by
  have hC : Nat.card C = 6048 := (Nat.card_congr eC.toEquiv).trans derived_g2_card
  cases h with
  | irreducible hp hf hi source _ =>
    exact ⟨hp, hf, hi, irreducible_marked_rows s.action eC source⟩
  | doubleThree F _ e _ _ => exact (not_sl_three F (eq_card_of_equiv hC e.groupEquiv)).elim
  | naturalDual n hn _ e => exact (not_binary_linear hC hn e.some.groupEquiv).elim
  | repeatedNatural n r hn _ _ _ e => exact (not_binary_linear hC hn e.some.groupEquiv).elim

/-- Restrict the same marked action to its original derived component. -/
theorem classification_natural {C : Subgroup D}
    (eC : C ≃* commutator (Atlas.G2.Model (ZMod 2))) (s : MovedSection ρ C)
    (h : ProjectiveLine.QuasisimpleActionCase ρ C s) :
    IsIrrPlus ρ C s.space.toSubmodule ∧ Function.Injective s.action ∧
      IsIrreducible (s.action.comp C.subtype) ∧
      Nonempty (ActionEquiv (s.action.comp C.subtype) (g2DerivedNatural (ZMod 2))) := by
  obtain ⟨hp, hf, hi, J, ⟨e⟩⟩ := classification_marked_rows ρ eC s h
  exact ⟨hp, hf, hi, ⟨derived_restriction s.action e⟩⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection.Action

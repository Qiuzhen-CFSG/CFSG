module
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.MarkedElimination.AlternatingSevenDimension.Orders
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts

/-!
# The A₇ component rows of B.5.1

An actual A₇ component has order 2520. The intrinsic model orders exclude
all reducible B.5.1 rows and all irreducible B.4.2 rows except the natural
seven-letter action and the exceptional four-dimensional action. The
natural row uses the marked S₇ action and restricts its coordinates to
the specified A₇ component; the whole actor need not be A₇.

The original moved section, its central quotient, faithfulness and component
irreducibility are retained. In particular no short-block hypothesis or
recognition premise enters the argument. This is the model-row comparison
used by the original small-model assembly before reconstructing its block.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.2,
printed p.86, B.5.1, pp.99–103, and the ordinary/exceptional A₇ cases of
13.6.22, printed p.932.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.MarkedElimination.AlternatingSevenDimension
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingModels
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

private theorem alt_card_ne {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8) :
    Nat.card (alternatingGroup (Fin n)) ≠ 2520 := by
  rcases hn with rfl | rfl | rfl <;> rw [nat_card_alternatingGroup] <;>
    norm_num [Nat.factorial]

private theorem eq_card_of_equiv {A B : Type*} [Group A] [Group B]
    (h : Nat.card A = 2520) (e : A ≃* B) : Nat.card B = 2520 :=
  (Nat.card_congr e.toEquiv).symm.trans h

private theorem not_binary_linear {A : Type*} [Group A] (hA : Nat.card A = 2520)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : A ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False := by
  rcases hn with rfl | rfl
  · exact not_sl_four (eq_card_of_equiv hA e)
  · exact not_sl_five (eq_card_of_equiv hA e)

private def alternating_restriction {C H : Subgroup D}
    (e : MarkedActionEquiv ρ H C (BinaryPermutation.naturalRepresentation (Fin 7))
      (alternatingGroup (Fin 7))) :
    ActionEquiv (ρ.comp C.subtype) (alternatingNatural 7) where
  groupEquiv := e.subgroupEquiv
  linearEquiv := e.action.linearEquiv
  intertwines c v := by
    have h := e.action.intertwines ⟨c, e.contained c.property⟩ v
    rw [e.compatible] at h
    exact h

/-- The marked A₇ component retains its natural seven-letter action or
its exceptional four-dimensional action in the original B.4.2 list. -/
theorem irreducible_marked_rows {C H : Subgroup D}
    (eC : C ≃* alternatingGroup (Fin 7))
    (h : ProjectiveLine.IrreducibleActionCase ρ C H) :
    (∃ J : Subgroup D, Nonempty (MarkedActionEquiv ρ J C
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7)))) ∨
      Module.finrank (ZMod 2) V = 4 := by
  have hC : Nat.card C = 2520 := (Nat.card_congr eC.toEquiv).trans alternating_card
  cases h with
  | linearTwo F _ e _ _ => exact (not_sl_two F (eq_card_of_equiv hC e.groupEquiv)).elim
  | linearThree F _ e _ => exact (not_sl_three F (eq_card_of_equiv hC e.groupEquiv)).elim
  | symplectic F _ _ e _ => exact (not_sp_four F (eq_card_of_equiv hC e.groupEquiv)).elim
  | symplecticTwo e _ =>
    exact (alt_card_ne (Or.inr (Or.inl rfl))
      (eq_card_of_equiv hC (e.subgroupEquiv.trans binarySymplecticDerivedEquiv))).elim
  | g2 F _ _ e _ _ => exact (not_g2 F (eq_card_of_equiv hC e.groupEquiv)).elim
  | g2Two e _ _ => exact (not_g2_derived (eq_card_of_equiv hC e.subgroupEquiv)).elim
  | symmetric n hn e _ _ =>
    rcases hn with rfl | rfl
    · exact (alt_card_ne (Or.inl rfl) (eq_card_of_equiv hC e.subgroupEquiv)).elim
    · exact Or.inl ⟨H, ⟨e⟩⟩
  | alternatingSix _ e _ _ =>
    exact (alt_card_ne (Or.inr (Or.inl rfl)) (eq_card_of_equiv hC e.groupEquiv)).elim
  | alternatingSeven _ _ _ hd _ _ => exact Or.inr hd
  | tripleSix _ a _ =>
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center C)
    rw [hC, Nat.card_congr a.quotientEquiv.toEquiv,
      Nat.card_congr a.centerEquiv.toEquiv, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial, Nat.card_congr Multiplicative.toAdd] at hc
  | binaryLinear n hn _ e _ => exact (not_binary_linear hC hn e.groupEquiv).elim
  | orthogonalSix _ _ e _ _ =>
    exact (alt_card_ne (Or.inr (Or.inr rfl)) (eq_card_of_equiv hC e.groupEquiv)).elim
  | symmetricEight _ e _ =>
    exact (alt_card_ne (Or.inr (Or.inr rfl)) (eq_card_of_equiv hC e.subgroupEquiv)).elim
  | exteriorFive _ _ e _ _ _ => exact (not_sl_five (eq_card_of_equiv hC e)).elim

/-- Restrict the same marked S₇ action to its original A₇ component. -/
theorem irreducible_group_rows {C H : Subgroup D}
    (eC : C ≃* alternatingGroup (Fin 7))
    (h : ProjectiveLine.IrreducibleActionCase ρ C H) :
    IsAlternatingNatural (ρ.comp C.subtype) 7 ∨ Module.finrank (ZMod 2) V = 4 := by
  rcases irreducible_marked_rows ρ eC h with ⟨_, ⟨e⟩⟩ | hd
  · exact Or.inl ⟨alternating_restriction ρ e⟩
  · exact Or.inr hd

/-- The reducible B.5.1 rows have different component groups. The surviving
section retains its actual irreducibility, faithfulness and action coordinates. -/
theorem classification_marked_rows {C : Subgroup D}
    (eC : C ≃* alternatingGroup (Fin 7)) (s : MovedSection ρ C)
    (h : ProjectiveLine.QuasisimpleActionCase ρ C s) :
    IsIrrPlus ρ C s.space.toSubmodule ∧ Function.Injective s.action ∧
      IsIrreducible (s.action.comp C.subtype) ∧
      ((∃ J : Subgroup D, Nonempty (MarkedActionEquiv s.action J C
        (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7)))) ∨
        Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4) := by
  have hC : Nat.card C = 2520 := (Nat.card_congr eC.toEquiv).trans alternating_card
  cases h with
  | irreducible hp hf hi source _ =>
    exact ⟨hp, hf, hi, irreducible_marked_rows s.action eC source⟩
  | doubleThree F _ e _ _ => exact (not_sl_three F (eq_card_of_equiv hC e.groupEquiv)).elim
  | naturalDual n hn _ e => exact (not_binary_linear hC hn e.some.groupEquiv).elim
  | repeatedNatural n r hn _ _ _ e => exact (not_binary_linear hC hn e.some.groupEquiv).elim

/-- The original natural-component alternative follows from the full marked
row while preserving all section properties. -/
theorem classification_group_rows {C : Subgroup D}
    (eC : C ≃* alternatingGroup (Fin 7)) (s : MovedSection ρ C)
    (h : ProjectiveLine.QuasisimpleActionCase ρ C s) :
    IsIrrPlus ρ C s.space.toSubmodule ∧ Function.Injective s.action ∧
      IsIrreducible (s.action.comp C.subtype) ∧
      (IsAlternatingNatural (s.action.comp C.subtype) 7 ∨
        Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4) := by
  obtain ⟨hp, hf, hi, hm⟩ := classification_marked_rows ρ eC s h
  refine ⟨hp, hf, hi, ?_⟩
  rcases hm with ⟨_, ⟨e⟩⟩ | hd
  · exact Or.inl ⟨alternating_restriction s.action e⟩
  · exact Or.inr hd

/-- Apply the group comparison to the exact section furnished by B.5.1. -/
theorem source_conclusion_rows {C : Subgroup D}
    (eC : C ≃* alternatingGroup (Fin 7))
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ C) :
    IsIrrPlus ρ C c.sectionData.space.toSubmodule ∧ Function.Injective c.sectionData.action ∧
      IsIrreducible (c.sectionData.action.comp C.subtype) ∧
      (IsAlternatingNatural (c.sectionData.action.comp C.subtype) 7 ∨
        Module.finrank (ZMod 2)
          (c.sectionData.space.toSubmodule ⧸ c.sectionData.central.toSubmodule) = 4) :=
  classification_group_rows ρ eC c.sectionData c.clause_one
/-- None of the nonsplit B.5.1 models has an A₇ component. -/
theorem nonsplit_impossible {C : Subgroup D} (eC : C ≃* alternatingGroup (Fin 7)) :
    ¬ NonsplitNatural (ρ.comp C.subtype) := by
  have hC : Nat.card C = 2520 := (Nat.card_congr eC.toEquiv).trans alternating_card
  intro h
  cases h with
  | linearTwo F h => exact not_sl_two F (eq_card_of_equiv hC h.some.groupEquiv)
  | symplectic F h => exact not_sp_four F (eq_card_of_equiv hC h.some.groupEquiv)
  | g2 F h => exact not_g2 F (eq_card_of_equiv hC h.some.groupEquiv)
  | alternatingSix h => exact alt_card_ne (Or.inr (Or.inl rfl)) (eq_card_of_equiv hC h.some.groupEquiv)
  | alternatingEight h => exact alt_card_ne (Or.inr (Or.inr rfl)) (eq_card_of_equiv hC h.some.groupEquiv)
  | derivedG2 h => exact not_g2_derived (eq_card_of_equiv hC h.some.groupEquiv)
  | linearThree h => exact not_sl_three BinaryField.two (eq_card_of_equiv hC h.some.groupEquiv)

/-- B.5.1(2) splits the original A₇ moved space from its full fixed space. -/
theorem source_split {C : Subgroup D} (eC : C ≃* alternatingGroup (Fin 7))
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ C) :
    IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ C) := by
  by_contra h
  exact nonsplit_impossible c.sectionData.action eC (c.clause_two h).2

/-- The same original section has zero central kernel. Thus the model rows
are actions on the full moved space, through its actual quotient map. -/
theorem source_central_eq_bot {C : Subgroup D} (eC : C ≃* alternatingGroup (Fin 7))
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ C) :
    c.sectionData.central.toSubmodule = ⊥ := by
  have hzero := (source_split ρ eC c).inf_eq_bot
  apply le_antisymm ?_ bot_le
  intro w hw
  have hfixed : (w : V) ∈ fixedSpace ρ C := by
    intro g
    exact congrArg Subtype.val ((c.sectionData.central_eq ▸ hw) g)
  have hz : (w : V) ∈ c.sectionData.space.toSubmodule ⊓ fixedSpace ρ C := ⟨w.property, hfixed⟩
  rw [hzero] at hz
  exact Subtype.ext hz

/-- The shorter supplement list is also incompatible with an A₇ component. -/
theorem supplement_impossible {C : Subgroup D} (eC : C ≃* alternatingGroup (Fin 7)) :
    ¬ SupplementNatural (ρ.comp C.subtype) := by
  intro h
  apply nonsplit_impossible ρ eC
  cases h with
  | symplectic F h => exact .symplectic F h
  | alternatingSix h => exact .alternatingSix h
  | alternatingEight h => exact .alternatingEight h
  | linearThree h => exact .linearThree h

/-- The complement is fixed by the entire original actor, as needed for
fixed-codimension transport from the original module to its moved space. -/
theorem source_invariant_split {C : Subgroup D} (eC : C ≃* alternatingGroup (Fin 7))
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ C) :
    IsCompl c.sectionData.space.toSubmodule ρ.invariants := by
  have hsup : c.sectionData.space.toSubmodule ⊔ ρ.invariants = ⊤ := by
    rcases c.clause_five with h | h
    · exact h
    · exact (supplement_impossible c.sectionData.action eC h.2.1).elim
  refine ⟨?_, codisjoint_iff.mpr hsup⟩
  apply (source_split ρ eC c).disjoint.mono_right
  intro w hw c
  exact hw c.val

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingModels

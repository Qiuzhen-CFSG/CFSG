module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection.Models
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.ComponentAction.Restriction

/-!
# The symplectic row in the full B.5.1 conclusion

All corrected B.4.2 rows are compared using their actual group isomorphisms.
Only the natural symplectic action survives. The three reducible alternatives
in B.5.1 have SL₃ or binary SL₄/SL₅ actors and are also excluded. Uniqueness
of the literal moved section transfers the resulting coordinates to any
construction of [V,C]/C_[V,C](C), without a splitting assumption on V.

Source: Aschbacher–Smith B.5.1, printed p.99, as used before 13.6.14 and
in 13.6.19, printed pp.929 and 931.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction
open Theory.SpecificGroups.SymplecticFour
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection

private theorem no_small_equiv {C X : Type*} [Group C] [Group X]
    {F : Type*} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m) (mark : C ≃* Sp F)
    (e : C ≃* X) (hx : Nat.card X ≤ 20160) : False := by
  have h := card_gt_small hF hm
  rw [← Nat.card_congr mark.toEquiv, Nat.card_congr e.toEquiv] at h
  omega

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C H : Subgroup D}
    {F : Type*} [Field F] [Finite F] {m : ℕ}

/-- Every corrected irreducible source row except the natural Sp₄ row is
excluded by the actual component isomorphism. -/
theorem irreducible_row (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (mark : C ≃* Sp F)
    (h : ProjectiveLine.IrreducibleActionCase ρ C H) :
    ∃ E : BinaryField, Nonempty (ActionEquiv (ρ.comp C.subtype) (binarySymplectic E)) := by
  cases h with
  | linearTwo E _ e _ _ =>
    exact (not_linearTwo hF (by omega) E ⟨mark.symm.trans e.groupEquiv⟩).elim
  | linearThree E _ e _ =>
    exact (not_linearThree hF (by omega) E ⟨mark.symm.trans e.groupEquiv⟩).elim
  | symplectic E _ _ e _ =>
    exact ⟨E, ⟨e⟩⟩
  | symplecticTwo e _ =>
    apply (no_small_equiv hF hm mark e.subgroupEquiv ?_).elim
    apply (Nat.card_le_card_of_injective _ (commutator
      (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype_injective).trans
    rw [Theory.SpecificGroups.SymplecticFour.card_sp, Nat.card_zmod]
    norm_num
  | g2 E _ _ e _ _ =>
    exact (not_g2 hF (by omega) E ⟨mark.symm.trans e.groupEquiv⟩).elim
  | g2Two e _ _ =>
    apply (no_small_equiv hF hm mark e.subgroupEquiv ?_).elim
    apply (Nat.card_le_card_of_injective _ (commutator
      (Atlas.G2.Model (ZMod 2))).subtype_injective).trans
    rw [Atlas.G2.card_Model, Nat.card_zmod]
    norm_num
  | symmetric n hn e _ _ =>
    apply (no_small_equiv hF hm mark e.subgroupEquiv ?_).elim
    rcases hn with rfl | rfl <;>
      rw [nat_card_alternatingGroup, Nat.card_fin] <;> norm_num [Nat.factorial]
  | alternatingSix _ e _ _ =>
    apply (no_small_equiv hF hm mark e.groupEquiv ?_).elim
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  | alternatingSeven _ _ e _ _ _ =>
    apply (no_small_equiv hF hm mark e ?_).elim
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  | tripleSix _ a _ =>
    have hc : Nat.card C ≤ 20160 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center C),
        Nat.card_congr a.quotientEquiv.toEquiv, Nat.card_congr a.centerEquiv.toEquiv,
        nat_card_alternatingGroup]
      norm_num [Nat.factorial, Nat.card_congr
        (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3)]
    exact (no_small_equiv hF hm mark (MulEquiv.refl C) hc).elim
  | binaryLinear d hd _ e _ =>
    exact (not_binary_linear hF hm hd ⟨mark.symm.trans e.groupEquiv⟩).elim
  | orthogonalSix _ _ e _ _ =>
    apply (no_small_equiv hF hm mark e.groupEquiv ?_).elim
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  | symmetricEight _ e _ =>
    apply (no_small_equiv hF hm mark e.subgroupEquiv ?_).elim
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  | exteriorFive _ _ e _ _ _ =>
    exact (not_binary_linear hF hm (Or.inr rfl) ⟨mark.symm.trans e⟩).elim


/-- Exhaust every B.5.1 action alternative on the actual moved quotient. -/
theorem action_case (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (mark : C ≃* Sp F) (s : MovedSection ρ C)
    (h : ProjectiveLine.QuasisimpleActionCase ρ C s) :
    ∃ E : BinaryField, Nonempty (ActionEquiv (s.action.comp C.subtype) (binarySymplectic E)) := by
  cases h with
  | irreducible _ _ _ h _ => exact irreducible_row hF hm mark h
  | doubleThree E _ e _ _ =>
    exact (not_linearThree hF (by omega) E ⟨mark.symm.trans e.groupEquiv⟩).elim
  | naturalDual d hd _ hn =>
    obtain ⟨e⟩ := hn
    exact (not_binary_linear hF hm hd ⟨mark.symm.trans e.groupEquiv⟩).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨e⟩ := hn
    exact (not_binary_linear hF hm hd ⟨mark.symm.trans e.groupEquiv⟩).elim

/-- The full corrected source conclusion gives natural coordinates on every
construction of the canonical component section. -/
theorem natural_of_quasisimple (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (mark : C ≃* Sp F) (s : MovedSection ρ C)
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ C) :
    ∃ E : BinaryField, Nonempty (ActionEquiv (s.action.comp C.subtype) (binarySymplectic E)) := by
  obtain ⟨E, he⟩ := action_case hF hm mark c.sectionData c.clause_one
  rw [LinearThree.MarkedAction.ComponentAction.movedSection_unique c.sectionData s] at he
  exact ⟨E, he⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection

module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives.Transport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve.ModelSeparation

/-!
# Group comparison in the full B.5.1 action list

Actual group equivalences and intrinsic order formulas eliminate the
incompatible actors. The triple-six row is excluded by its nontrivial
center. This leaves four possible actions: the A₈ natural central quotient,
the binary-four natural central quotient, natural plus dual in dimension
four, and positive repeated binary-four naturals on the upper space.
The surviving action equivalences are retained literally; group order is
not used to identify a representation.

The source-correct projective-line contracts are used throughout. The
imported cardinal comparisons are intrinsic calculations and require no
Chapter 15 source theorem or strong-offender hypothesis. In particular
the ratio-one orthogonal row is retained.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2,
printed p.86, B.5.1, pp.99–103, applied following 13.6.23, p.933/PDF p.950.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve (sl_two_card_ne sl_three_card_ne psl_five_card_ne card_of_alternating)

private theorem sl_two_field_card_ne (F : BinaryField) : Nat.card SL(2,F.Carrier) ≠ 20160 := by
  let e := (GaloisField.algEquivGaloisField 2 F.degree F.card_eq).toRingEquiv
  rw [Nat.card_congr (Atlas.fieldEquivSL 2 e).toEquiv]
  exact sl_two_card_ne F.degree F.degree_pos

private theorem sl_three_field_card_ne (F : BinaryField) : Nat.card SL(3,F.Carrier) ≠ 20160 := by
  let e := (GaloisField.algEquivGaloisField 2 F.degree F.card_eq).toRingEquiv
  rw [Nat.card_congr (Atlas.fieldEquivSL 3 e).toEquiv]
  exact sl_three_card_ne F.degree F.degree_pos

private theorem sl_five_card_ne : Nat.card SL(5,ZMod 2) ≠ 20160 := by
  rw [Nat.card_congr (binaryProjectiveEquiv 5 (by decide)).toEquiv]
  exact psl_five_card_ne

private theorem power_product_mono {q q' : ℕ} (h : q ≤ q') (a b c : ℕ) :
    q ^ a * (q ^ b - 1) * (q ^ c - 1) ≤
      q' ^ a * (q' ^ b - 1) * (q' ^ c - 1) :=
  Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left h a)
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h b) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h c) 1)

private theorem symplectic_field_card_ne (F : BinaryField) (hf : 1 < F.degree) :
    Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier) ≠ 20160 := by
  rw [Theory.SpecificGroups.SymplecticFour.card_sp, F.card_eq]
  have hq : 4 ≤ 2 ^ F.degree := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ F.degree)
  have hh := power_product_mono hq 4 2 4
  omega

private theorem g2_field_card_ne (F : BinaryField) (hf : 1 < F.degree) :
    Nat.card (Atlas.G2.Model F.Carrier) ≠ 20160 := by
  rw [Atlas.G2.card_Model, F.card_eq]
  have hq : 4 ≤ 2 ^ F.degree := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ F.degree)
  have hh := power_product_mono hq 6 6 2
  omega

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (eD : D ≃* alternatingGroup (Fin 8))

include eD

/-- An A₈ actor leaves precisely the orthogonal and binary-four natural
irreducible rows, with their actual intertwining coordinates. -/
theorem irreducible_group_rows {J : Subgroup D}
    (h : ProjectiveLine.IrreducibleActionCase ρ ⊤ J) :
    IsAlternatingNatural (ρ.comp (⊤ : Subgroup D).subtype) 8 ∨
      IsLinearNatural (ρ.comp (⊤ : Subgroup D).subtype) BinaryField.two 4 := by
  have hcard := card_of_alternating eD
  have htop : Nat.card (⊤ : Subgroup D) = 20160 :=
    (Nat.card_congr Subgroup.topEquiv.toEquiv).trans hcard
  cases h with
  | linearTwo F _ e _ _ =>
    exact (sl_two_field_card_ne F ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans htop)).elim
  | linearThree F _ e _ =>
    exact (sl_three_field_card_ne F ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans htop)).elim
  | symplectic F hf _ e _ =>
    exact (symplectic_field_card_ne F hf ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans htop)).elim
  | symplecticTwo e _ =>
    have hc := Nat.card_congr (e.subgroupEquiv.trans binarySymplecticDerivedEquiv).toEquiv
    rw [htop, nat_card_alternatingGroup, Nat.card_fin] at hc
    norm_num at hc
  | g2 F hf _ e _ _ =>
    exact (g2_field_card_ne F hf ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans htop)).elim
  | g2Two e _ _ =>
    have hc := (commutator (Atlas.G2.Model (ZMod 2))).card_le_card_group
    rw [← Nat.card_congr e.subgroupEquiv.toEquiv, htop, Atlas.G2.card_Model, Nat.card_zmod] at hc
    norm_num at hc
  | symmetric n hn e _ _ =>
    have hc := Nat.card_congr e.subgroupEquiv.toEquiv
    rcases hn with rfl | rfl <;>
      rw [htop, nat_card_alternatingGroup, Nat.card_fin] at hc <;> norm_num at hc
  | alternatingSix _ e _ _ =>
    have hc := Nat.card_congr e.groupEquiv.toEquiv
    rw [htop, nat_card_alternatingGroup, Nat.card_fin] at hc
    norm_num at hc
  | alternatingSeven _ _ e _ _ _ =>
    have hc := Nat.card_congr e.toEquiv
    rw [htop, nat_card_alternatingGroup, Nat.card_fin] at hc
    norm_num at hc
  | tripleSix _ a _ =>
    have hc := Nat.card_congr (Subgroup.centerCongr (Subgroup.topEquiv.trans eD)).toEquiv
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.card_bot] at hc
    have h3 : Nat.card (center (⊤ : Subgroup D)) = 3 := by
      simpa using Nat.card_congr a.centerEquiv.toEquiv
    omega
  | binaryLinear n hn _ e _ =>
    rcases hn with rfl | rfl
    · exact Or.inr ⟨e⟩
    · exact (sl_five_card_ne ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans htop)).elim
  | orthogonalSix _ _ e _ _ => exact Or.inl ⟨e⟩
  | symmetricEight _ e _ =>
    have hc := J.card_le_card_group
    rw [Nat.card_congr e.action.groupEquiv.toEquiv, hcard,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at hc
    norm_num at hc
  | exteriorFive _ _ e _ _ _ =>
    exact (sl_five_card_ne ((Nat.card_congr e.toEquiv).symm.trans htop)).elim

/-- Group comparison preserves every module row with the A₈ actor.
The remaining natural actions are not identified from their group order. -/
theorem classification_group_rows (s : MovedSection ρ ⊤)
    (h : ProjectiveLine.QuasisimpleActionCase ρ ⊤ s) :
    IsAlternatingNatural (s.action.comp (⊤ : Subgroup D).subtype) 8 ∨
      IsLinearNatural (s.action.comp (⊤ : Subgroup D).subtype) BinaryField.two 4 ∨
      IsNaturalPlusDual (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype) 4 ∨
      ∃ r, 0 < r ∧ r ≤ 3 ∧ IsRepeatedLinearNatural
        (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype) BinaryField.two 4 r := by
  have htop : Nat.card (⊤ : Subgroup D) = 20160 :=
    (Nat.card_congr Subgroup.topEquiv.toEquiv).trans (card_of_alternating eD)
  cases h with
  | irreducible _ _ _ hs _ =>
    rcases irreducible_group_rows s.action eD hs with hn | hn
    · exact Or.inl hn
    · exact Or.inr (Or.inl hn)
  | doubleThree F _ e _ _ =>
    exact (sl_three_field_card_ne F ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans htop)).elim
  | naturalDual n hn _ hnatural =>
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl hnatural))
    · obtain ⟨e⟩ := hnatural
      exact (sl_five_card_ne ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans htop)).elim
  | repeatedNatural n r hn hr hb _ hnatural =>
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr ⟨r, hr, hb, hnatural⟩))
    · obtain ⟨e⟩ := hnatural
      exact (sl_five_card_ne ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans htop)).elim

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives

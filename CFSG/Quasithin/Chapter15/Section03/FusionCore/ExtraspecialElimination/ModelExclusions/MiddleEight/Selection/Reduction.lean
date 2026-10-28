module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Inputs
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve.ModelSeparation

/-!
# The strong-offender sieve for the A₈ component

Apply B.5.1 to the actual offender-generated component. Strict offending
survives restriction to its moved space and passage to the central quotient.
Consequently the ratio-one rows of B.4.2, including its orthogonal row, and
the double-natural SL₃ row of B.5.1 are impossible. Actual group orders
exclude the remaining SL₃ and Sp₄ actors, the symmetric extension on this
component actor, and degree five.

The output retains all three surviving module possibilities: a natural
central quotient, natural plus dual, and repeated natural modules in degree
four. It does not assert that the marked-point geometry excludes either
natural branch; that additional deduction is still required for selection.
No cohomology or B.5.1(6) no-offender conclusion is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2,
printed p.86, B.5.1(1), pp.99–103, and the proof of 15.3.49, p.1145.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve (psl_five_card_ne card_of_alternating)
open Chapter2.ComponentRefinement.LieType.Binary

private theorem sl_three_card_ne (F : BinaryField) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) ≠ 20160 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
  rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin] at h
  have hc := h.trans (Matrix.PSL3.LinearThree.card_projective_mul_scalar F.Carrier)
  rw [hc, F.card_eq]
  intro he
  have hb : F.degree < 2 := by
    by_contra hn
    have hq : 4 ≤ 2 ^ F.degree := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ F.degree)
    have hh := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    omega
  have hd : F.degree = 1 := by have := F.degree_pos; omega
  norm_num [hd] at he

private theorem symplectic_card_ne (F : BinaryField) (hf : 1 < F.degree) :
    Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier) ≠ 20160 := by
  rw [Theory.SpecificGroups.SymplecticFour.card_sp, F.card_eq]
  have hq : 4 ≤ 2 ^ F.degree := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ F.degree)
  have hh := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.pow_le_pow_left hq 4)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1)
  omega

/-- The degree-five special linear carrier cannot be the actual A₈ component. -/
theorem sl_five_card_ne : Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ≠ 20160 := by
  rw [Nat.card_congr (binaryProjectiveEquiv 5 (by decide)).toEquiv]
  exact psl_five_card_ne

variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

omit [Finite D] in
/-- Strict offending descends to the literal central quotient of the moved space. -/
theorem strong_on_movedQuotient (s : MovedSection ρ ⊤)
    {A : Subgroup D} (hA : IsStrongOffender ρ A) : IsStrongOffender s.action A := by
  refine ⟨hA.1, ?_⟩
  have hs := fixedCodim_subrepresentation_le ρ s.space A
  have hq := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A
  exact (le_trans (Nat.le_add_right _ _) (hq.trans hs)).trans_lt hA.2

/-- Among B.4.2's complete rows, a strong offender on an A₈ actor leaves
only the four-dimensional natural action. In particular the orthogonal
ratio-one row is excluded on its actual quotient. -/
theorem select_irreducible (hcard : Nat.card D = 20160)
    (hstrong : IsStrongFFModule ρ) {J : Subgroup D}
    (h : IrreducibleActionCase ρ ⊤ J) :
    Nonempty (ActionEquiv (ρ.comp (⊤ : Subgroup D).subtype)
      (linearNatural BinaryField.two 4)) := by
  have hratio := (isStrongFFModule_iff_quadraticRatio_lt_one ρ).mp hstrong
  have htop : Nat.card (⊤ : Subgroup D) = 20160 := (Nat.card_congr Subgroup.topEquiv.toEquiv).trans hcard
  cases h with
  | linearTwo _ _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | linearThree F _ e _ =>
    exact (sl_three_card_ne F ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans htop)).elim
  | symplectic F hf _ e _ =>
    exact (symplectic_card_ne F hf ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans htop)).elim
  | symplecticTwo e _ =>
    have hc := Nat.card_congr (e.subgroupEquiv.trans binarySymplecticDerivedEquiv).toEquiv
    rw [htop, nat_card_alternatingGroup, Nat.card_fin] at hc
    norm_num at hc
  | g2 _ _ _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | g2Two _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | symmetric _ _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | alternatingSix _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | alternatingSeven _ _ _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | tripleSix _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | binaryLinear n hn _ e _ =>
    rcases hn with rfl | rfl
    · exact ⟨e⟩
    · exact (sl_five_card_ne ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans htop)).elim
  | orthogonalSix _ _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | symmetricEight _ e _ =>
    have hc := J.card_le_card_group
    rw [Nat.card_congr e.action.groupEquiv.toEquiv, hcard,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at hc
    norm_num at hc
  | exteriorFive _ _ _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim

/-- The surviving alternatives retain the source's literal moved space and
central quotient. Neither a central splitting nor local coordinates are assumed. -/
def RemainingCases (s : MovedSection ρ ⊤) : Prop :=
  Nonempty (ActionEquiv (s.action.comp (⊤ : Subgroup D).subtype)
    (linearNatural BinaryField.two 4)) ∨
  IsNaturalPlusDual (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype) 4 ∨
  ∃ r, 0 < r ∧ r ≤ 3 ∧ IsRepeatedLinearNatural
    (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype) BinaryField.two 4 r

/-- All four B.5.1 alternatives have been processed. The remaining two
natural branches still need the marked-point geometric exclusion. -/
theorem remaining_cases (hcard : Nat.card D = 20160)
    (hstrong : IsStrongFFModule ρ) (s : MovedSection ρ ⊤)
    (h : QuasisimpleActionCase ρ ⊤ s) : RemainingCases ρ s := by
  have hratio := (isStrongFFModule_iff_quadraticRatio_lt_one ρ).mp hstrong
  have htop : Nat.card (⊤ : Subgroup D) = 20160 := (Nat.card_congr Subgroup.topEquiv.toEquiv).trans hcard
  cases h with
  | irreducible _ _ _ hs _ =>
    obtain ⟨A, hA⟩ := hstrong
    exact Or.inl (select_irreducible s.action hcard ⟨A, strong_on_movedQuotient ρ s hA⟩ hs)
  | doubleThree _ _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | naturalDual n hn _ hnatur =>
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl hnatur)
    · obtain ⟨e⟩ := hnatur
      exact (sl_five_card_ne ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans htop)).elim
  | repeatedNatural n r hn hr hb _ hnatur =>
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inr ⟨r, hr, hb, hnatur⟩)
    · obtain ⟨e⟩ := hnatur
      exact (sl_five_card_ne ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans htop)).elim

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection

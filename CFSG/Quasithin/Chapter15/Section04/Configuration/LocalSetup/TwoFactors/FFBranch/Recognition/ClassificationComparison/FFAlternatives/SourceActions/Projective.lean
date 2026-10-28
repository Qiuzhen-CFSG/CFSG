module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.QuasisimpleModels
public import Theory.SpecificGroups.FFLinearPrimeCore
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Projective comparisons for the source FF alternatives

The scalar centers vanish for SL₂ in characteristic two, SL₃ over fields of
odd binary degree, and SLₙ(2). Thus the quotient maps give actual SL/PSL
isomorphisms. These comparisons justify the projective notation in B.4.2
and B.5.6; they do not classify modules.

Source: Aschbacher–Smith, B.4.2, p.86, and B.5.6, p.105.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

/-- The four-element coefficient field. -/
noncomputable def BinaryField.four : BinaryField where
  Carrier := GaloisField 2 2
  degree := 2
  degree_pos := by decide
  card_eq := GaloisField.card 2 2 (by decide)

/-- In odd binary degree, three does not divide the scalar-center order. -/
theorem sl_three_center_eq_bot (F : BinaryField) (ho : Odd F.degree) :
    center SL(3,F.Carrier) = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  rw [Atlas.ExceptionalSupport.card_sl_center, F.card_eq]
  simp only [Fintype.card_fin]
  have hm : 2 ^ F.degree % 3 = 2 := by
    obtain ⟨k, hk⟩ := ho
    rw [hk, pow_add, pow_mul]
    have h : (2 ^ 2) ^ k % 3 = 1 := by
      have h := (show Nat.ModEq 3 4 1 from by decide).pow k
      simpa [Nat.ModEq] using h
    rw [Nat.mul_mod, h]
    simp
  apply Nat.Coprime.gcd_eq_one
  apply (by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  have hp : 0 < 2 ^ F.degree := pow_pos (by decide) _
  omega

/-- Every binary special linear group has trivial scalar center. -/
theorem sl_binary_center_eq_bot (d : ℕ) (hd : 0 < d) :
    center SL(d,ZMod 2) = ⊥ := by
  let : NeZero d := ⟨by omega⟩
  apply eq_bot_iff.mpr
  intro g hg
  obtain ⟨c, hc, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have hc1 : c = 1 := by
    have hc0 : c ≠ 0 := by
      intro h
      simp [h, hd.ne'] at hc
    fin_cases c
    · exact False.elim (hc0 rfl)
    · rfl
  apply Subtype.ext
  simpa [hc1] using he.symm

/-- The canonical inverse of the quotient by a trivial scalar center. -/
noncomputable def slProjectiveEquiv {d : ℕ} {F : Type*} [Field F]
    (h : center SL(d,F) = ⊥) : SL(d,F) ≃* PSL(d,F) :=
  ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).symm

noncomputable def linearTwoProjectiveEquiv (F : BinaryField) :
    SL(2,F.Carrier) ≃* PSL(2,F.Carrier) :=
  slProjectiveEquiv Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot

noncomputable def oddLinearThreeProjectiveEquiv (F : BinaryField) (ho : Odd F.degree) :
    SL(3,F.Carrier) ≃* PSL(3,F.Carrier) :=
  slProjectiveEquiv (sl_three_center_eq_bot F ho)

noncomputable def binaryProjectiveEquiv (d : ℕ) (hd : 0 < d) :
    SL(d,ZMod 2) ≃* PSL(d,ZMod 2) := slProjectiveEquiv (sl_binary_center_eq_bot d hd)

/-- The small alternating model really is the even rank-one matrix group. -/
noncomputable def alternatingFiveLinearEquiv :
    alternatingGroup (Fin 5) ≃* SL(2,BinaryField.four.Carrier) :=
  (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := BinaryField.four.Carrier) (by
      change Nat.card (GaloisField 2 2) = 4
      rw [GaloisField.card 2 2 (by decide)]
      decide)).some.symm.trans (linearTwoProjectiveEquiv BinaryField.four).symm

/-- The orthogonal A₈ model has the actual binary rank-four actor. -/
noncomputable def alternatingEightLinearEquiv :
    alternatingGroup (Fin 8) ≃* SL(4,ZMod 2) :=
  Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans (binaryProjectiveEquiv 4 (by decide)).symm

/-- The existing factor interface gives the source's projective models by
actual equivalences, including the odd-degree restriction in rank three. -/
theorem FactorModel.projectiveCases {D : Type*} [Group D] (h : FactorModel D) :
    (∃ F : BinaryField, Nonempty (D ≃* PSL(2,F.Carrier))) ∨
      Nonempty (D ≃* Equiv.Perm (Fin 5)) ∨
      ∃ F : BinaryField, Odd F.degree ∧ Nonempty (D ≃* PSL(3,F.Carrier)) := by
  cases h with
  | linearTwo F e => exact Or.inl ⟨F, ⟨e.trans (linearTwoProjectiveEquiv F)⟩⟩
  | symmetricFive e => exact Or.inr (Or.inl ⟨e⟩)
  | linearThree F ho e =>
    exact Or.inr (Or.inr ⟨F, ho, ⟨e.trans (oddLinearThreeProjectiveEquiv F ho)⟩⟩)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

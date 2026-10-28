module
public import Theory.SpecificGroups.HeisenbergPrime
public import Theory.Alternating.Aut
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Theory.SpecificGroups.BinaryLinear.OuterTwo
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Small automorphism groups exclude the ternary Heisenberg group

The actual automorphism groups of A₅–A₈ and SL₅(2) have orders not divisible by 27.
For the alternating groups this follows from the permutation description,
including the exceptional A₆ automorphism group. For SL₅(2), the outer
quotient is a two-group and the inner group has order dividing |SL₅(2)|.
Consequently none admits a faithful action of the Heisenberg group of order 27.

Source application: Aschbacher–Smith, 14.7.26, printed p.1053,
refs/quasithin.pdf, the finite rows of the C.2.7 automorphism exclusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace HeisenbergPrime.SmallAutomorphismExclusions

/-- The four small alternating automorphism groups have no factor of 27. -/
theorem alternating_not_three_cube {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    ¬ 27 ∣ Nat.card (MulAut (alternatingGroup (Fin n))) := by
  by_cases h6 : n = 6
  · subst n
    rw [AlternatingSix.ShadowLocal.card_aut]
    decide
  let e : Equiv.Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n (by omega) h6)
  rw [←Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rcases hn with rfl | rfl | rfl | rfl <;> norm_num [Nat.factorial] at *

/-- The binary degree-five linear automorphism group has no factor of 27. -/
theorem binary_five_not_three_cube : ¬ 27 ∣ Nat.card (MulAut SL(5,ZMod 2)) := by
  let I := MulAut.innerSubgroup SL(5,ZMod 2)
  have hc : Nat.card SL(5,ZMod 2) = 9999360 := by
    let e := (BinaryLinear.OuterCyclic.slEquivLinear 5).trans
      (BinaryLinear.OuterCyclic.matrixEquivLinear 5).symm
    rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
    decide
  have hI : Nat.card I ∣ 9999360 := hc ▸ card_range_dvd (MulAut.conj (G := SL(5,ZMod 2)))
  obtain ⟨k,hk⟩ := (BinaryLinear.OuterCyclic.sl_outer_isTwoGroup (Or.inr rfl : 5 = 4 ∨ 5 = 5)).exists_card_eq
  have hi : I.index = 2^k := hk
  intro hd
  rw [←I.card_mul_index,hi] at hd
  have h27 : 27 ∣ Nat.card I := (show Nat.Coprime 27 (2^k) from
    (by decide : Nat.Coprime 27 2).pow_right k).dvd_of_dvd_mul_right hd
  exact (by decide : ¬27 ∣ 9999360) (h27.trans hI)

/-- No ternary Heisenberg group acts faithfully on these alternating groups. -/
theorem no_alternating_action {A : Type*} [Group A]
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) (e : A ≃* alternatingGroup (Fin n))
    (f : HeisenbergPrime 3 →* MulAut A) (hf : Function.Injective f) : False := by
  have hd := card_dvd_of_injective f hf
  rw [HeisenbergPrime.card, Nat.card_congr (MulAut.congr e).toEquiv] at hd
  exact alternating_not_three_cube hn hd

/-- No ternary Heisenberg group acts faithfully on SL₅(2). -/
theorem no_binary_five_action {A : Type*} [Group A] (e : A ≃* SL(5,ZMod 2))
    (f : HeisenbergPrime 3 →* MulAut A) (hf : Function.Injective f) : False := by
  have hd := card_dvd_of_injective f hf
  rw [HeisenbergPrime.card, Nat.card_congr (MulAut.congr e).toEquiv] at hd
  exact binary_five_not_three_cube hd
end HeisenbergPrime.SmallAutomorphismExclusions

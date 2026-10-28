module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.NaturalLayerOrders
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Distinguishing the nonbinary symplectic row by order

The two-part of the classical order formulas identifies the possible field
degrees. Cancelling the resulting common odd factor excludes SL₃ and G₂;
a strict product comparison excludes SL₂. The binary linear exceptions
have two-parts 2⁶ and 2¹⁰, incompatible with the symplectic two-part 2⁴ⁿ.
These tests retain arbitrary nonbinary degree and feed the actual FF action
recognition, before the later pushing-up argument restricts the field to four.

Source: Aschbacher--Smith B.4.2, B.5.1 and C.1.32; the classical group order
formulas are proved in the imports.
-/

public section
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource

private theorem twoPart_eq {a b c d : ℕ} (hc : Odd c) (hd : Odd d)
    (h : 2 ^ a * c = 2 ^ b * d) : a = b := by
  have he := congrArg (fun k : ℕ => k.factorization 2) h
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd
  rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) hc0,
    Nat.factorization_mul (pow_ne_zero _ (by decide)) hd0] at he
  simpa only [Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hc.not_two_dvd_nat,
    Nat.factorization_eq_zero_of_not_dvd hd.not_two_dvd_nat, add_zero] using he

private theorem odd_pow_sub_one {n : ℕ} (hn : 0 < n) : Odd (2 ^ n - 1) := by
  apply (Nat.odd_sub' (Nat.one_le_two_pow)).mpr
  exact iff_of_true odd_one ((show Even (2 : ℕ) by decide).pow_of_ne_zero hn.ne')

private theorem triple_ne {n d a : ℕ} (hn : 0 < n) (hd : 0 < d)
    (ha : 0 < a) (ha4 : a ≠ 4) :
    2 ^ (4*n) * (2 ^ (2*n) - 1) * (2 ^ (4*n) - 1) ≠
      2 ^ (a*d) * (2 ^ (a*d) - 1) * (2 ^ (2*d) - 1) := by
  intro he
  have hv : 4*n = a*d := twoPart_eq
    ((odd_pow_sub_one (by omega : 0 < 2*n)).mul (odd_pow_sub_one (by omega : 0 < 4*n)))
    ((odd_pow_sub_one (Nat.mul_pos ha hd)).mul (odd_pow_sub_one (by omega : 0 < 2*d)))
    (by simpa only [mul_assoc] using he)
  rw [←hv] at he
  have hc := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (4*n))
    (show 2 ^ (4*n) * ((2 ^ (2*n) - 1) * (2 ^ (4*n) - 1)) =
      2 ^ (4*n) * ((2 ^ (4*n) - 1) * (2 ^ (2*d) - 1)) by
      simpa only [mul_assoc] using he)
  have hz : 0 < 2 ^ (4*n) - 1 := Nat.sub_pos_of_lt
    (Nat.one_lt_two_pow (by omega : 4*n ≠ 0))
  rw [mul_comm (2 ^ (2*n) - 1)] at hc
  have hl := Nat.eq_of_mul_eq_mul_left hz hc
  have hp : 2 ^ (2*n) = 2 ^ (2*d) := by
    have h1 := Nat.one_le_two_pow (n := 2*n)
    have h2 := Nat.one_le_two_pow (n := 2*d)
    omega
  have hn' := Nat.pow_right_injective (by decide : 1 < (2:ℕ)) hp
  have hnd : n = d := by omega
  subst d
  have haeq : 4 = a := Nat.eq_of_mul_eq_mul_right hn hv
  exact ha4 haeq.symm

private theorem linear_two_ne {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    2 ^ (4*n) * (2 ^ (2*n) - 1) * (2 ^ (4*n) - 1) ≠
      2 ^ d * (2 ^ (2*d) - 1) := by
  intro he
  have hv : 4*n = d := twoPart_eq
    ((odd_pow_sub_one (by omega : 0 < 2*n)).mul (odd_pow_sub_one (by omega : 0 < 4*n)))
    (odd_pow_sub_one (by omega : 0 < 2*d))
    (by simpa only [mul_assoc] using he)
  rw [←hv] at he
  have hc := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (4*n))
    (show 2 ^ (4*n) * ((2 ^ (2*n) - 1) * (2 ^ (4*n) - 1)) =
      2 ^ (4*n) * (2 ^ (2*(4*n)) - 1) by simpa only [mul_assoc] using he)
  have hlt : (2 ^ (2*n) - 1) * (2 ^ (4*n) - 1) <
      2 ^ (4*n) * 2 ^ (4*n) - 1 := by
    have ha : 2 ^ (2*n) ≤ 2 ^ (4*n) := Nat.pow_le_pow_right (by decide) (by omega)
    have hb : 1 < 2 ^ (4*n) := Nat.one_lt_two_pow (by omega)
    have hsmall : (2 ^ (2*n) - 1) * (2 ^ (4*n) - 1) ≤ (2 ^ (4*n) - 1)^2 := by
      rw [pow_two]
      gcongr
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ (4*n))
    have hs' := Nat.sub_add_cancel (show 1 ≤ 2 ^ (4*n) * 2 ^ (4*n) by nlinarith)
    nlinarith
  rw [←pow_add, show 4*n+4*n = 2*(4*n) by omega] at hlt
  omega

private theorem symplectic_degree {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (he : 2 ^ (4*n) * (2 ^ (2*n) - 1) * (2 ^ (4*n) - 1) =
      2 ^ (4*d) * (2 ^ (2*d) - 1) * (2 ^ (4*d) - 1)) : n = d := by
  have hv := twoPart_eq
    ((odd_pow_sub_one (by omega : 0 < 2*n)).mul (odd_pow_sub_one (by omega : 0 < 4*n)))
    ((odd_pow_sub_one (by omega : 0 < 2*d)).mul (odd_pow_sub_one (by omega : 0 < 4*d)))
    (by simpa only [mul_assoc] using he)
  omega

private theorem binary_six_ten_ne {n : ℕ} (hn : 0 < n) {a c : ℕ}
    (ha : a = 6 ∨ a = 10) (hc : Odd c) :
    2 ^ (4*n) * (2 ^ (2*n) - 1) * (2 ^ (4*n) - 1) ≠ 2 ^ a * c := by
  intro he
  have hv := twoPart_eq
    ((odd_pow_sub_one (by omega : 0 < 2*n)).mul (odd_pow_sub_one (by omega : 0 < 4*n))) hc
    (by simpa only [mul_assoc] using he)
  omega


private theorem card_sl_three (E : Type*) [Field E] [Finite E] :
    Nat.card SL(3,E) =
      Nat.card E ^ 3 * (Nat.card E ^ 3 - 1) * (Nat.card E ^ 2 - 1) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(3,E)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Matrix.PSL3.LinearThree.card_projective_mul_scalar E

private theorem binary_card (d : ℕ) :
    Nat.card SL(d,ZMod 2) = ∏ i : Fin d, (2^d - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear d).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear d).toEquiv,
    Matrix.card_GL_field]
  simp

variable (F : Type*) [Field F] [Finite F] {n : ℕ} (hc : Nat.card F = 2 ^ n)

include hc

private theorem symplectic_card :
    Nat.card (Matrix.symplecticGroup (Fin 2) F) =
      2 ^ (4*n) * (2 ^ (2*n) - 1) * (2 ^ (4*n) - 1) := by
  rw [Theory.SpecificGroups.SymplecticFour.card_sp,hc]
  simp only [←pow_mul, Nat.mul_comm n]

/-- Every nonbinary symplectic row has at least the order of Sp₄(4). -/
theorem card_symplectic_ge (hn : 1 < n) :
    979200 ≤ Nat.card (Matrix.symplecticGroup (Fin 2) F) := by
  have hq : 4 ≤ Nat.card F := by
    rw [hc]
    change 2 ^ 2 ≤ 2 ^ n
    exact Nat.pow_le_pow_right (by decide) hn
  rw [Theory.SpecificGroups.SymplecticFour.card_sp]
  calc
    979200 = 4^4 * (4^2-1) * (4^4-1) := by norm_num
    _ ≤ _ := by gcongr

/-- The binary SL₂ natural row has a different order. -/
theorem card_symplectic_ne_sl_two (hn : 0 < n) (E : BinaryField) :
    Nat.card (Matrix.symplecticGroup (Fin 2) F) ≠ Nat.card SL(2,E.Carrier) := by
  rw [symplectic_card F hc,Atlas.card_sl_two,E.card_eq]
  simpa only [←pow_mul, Nat.mul_comm E.degree] using linear_two_ne hn E.degree_pos

/-- The binary SL₃ rows have a different order. -/
theorem card_symplectic_ne_sl_three (hn : 0 < n) (E : BinaryField) :
    Nat.card (Matrix.symplecticGroup (Fin 2) F) ≠ Nat.card SL(3,E.Carrier) := by
  rw [symplectic_card F hc,card_sl_three,E.card_eq]
  simpa only [←pow_mul, Nat.mul_comm E.degree] using
    triple_ne hn E.degree_pos (by decide : 0 < 3) (by decide : 3 ≠ 4)

/-- The binary G₂ natural row has a different order. -/
theorem card_symplectic_ne_g2 (hn : 0 < n) (E : BinaryField) :
    Nat.card (Matrix.symplecticGroup (Fin 2) F) ≠ Nat.card (Atlas.G2.Model E.Carrier) := by
  rw [symplectic_card F hc,Atlas.G2.card_Model,E.card_eq]
  simpa only [←pow_mul, Nat.mul_comm E.degree] using
    triple_ne hn E.degree_pos (by decide : 0 < 6) (by decide : 6 ≠ 4)

/-- Equality of symplectic orders preserves the supplied binary field degree. -/
theorem degree_eq_of_card_symplectic (hn : 0 < n) (E : BinaryField)
    (he : Nat.card (Matrix.symplecticGroup (Fin 2) F) =
      Nat.card (Matrix.symplecticGroup (Fin 2) E.Carrier)) : E.degree = n := by
  rw [symplectic_card F hc,symplectic_card E.Carrier E.card_eq] at he
  exact (symplectic_degree hn E.degree_pos he).symm

/-- Neither exceptional binary linear rank can equal a symplectic order. -/
theorem card_symplectic_ne_binary_higher (hn : 0 < n) {d : ℕ} (hd : d = 4 ∨ d = 5) :
    Nat.card (Matrix.symplecticGroup (Fin 2) F) ≠ Nat.card SL(d,ZMod 2) := by
  rw [symplectic_card F hc]
  rcases hd with rfl | rfl
  · have he : Nat.card SL(4,ZMod 2) = 2^6 * 315 := by
      rw [binary_card]
      norm_num [Fin.prod_univ_succ]
    rw [he]
    exact binary_six_ten_ne hn (Or.inl rfl) (by decide)
  · have he : Nat.card SL(5,ZMod 2) = 2^10 * 9765 := by
      rw [binary_card]
      norm_num [Fin.prod_univ_succ]
    rw [he]
    exact binary_six_ten_ne hn (Or.inr rfl) (by decide)

/-- The small alternating endpoints are all below the nonbinary symplectic order. -/
theorem card_symplectic_ne_alternating (hn : 1 < n) {d : ℕ}
    (hd : d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8) :
    Nat.card (Matrix.symplecticGroup (Fin 2) F) ≠ Nat.card (alternatingGroup (Fin d)) := by
  have hlo := card_symplectic_ge F hc hn
  intro he
  rw [he] at hlo
  rcases hd with rfl | rfl | rfl | rfl <;>
    rw [nat_card_alternatingGroup] at hlo <;> norm_num [Nat.factorial] at hlo

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

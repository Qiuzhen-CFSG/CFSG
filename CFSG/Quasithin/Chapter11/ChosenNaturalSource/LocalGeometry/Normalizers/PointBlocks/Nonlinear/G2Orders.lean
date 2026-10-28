module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OrderRecognition

/-!
# Identifying the exceptional point quotient by its order

The two-part of the genuine G₂ order distinguishes the linear rows of B.4.2
and fixes the degree in its exceptional row. The symplectic comparison reuses
the proved nonbinary order sieve. These are the numerical inputs to recognizing
the literal point-pair central omega action; no MS classification is assumed.
Source: Aschbacher--Smith B.4.2, B.5.1 and 11.1.5, pp.765--766.
-/

public section
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear
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

private theorem triple_ne {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    2 ^ (6*n) * (2 ^ (6*n) - 1) * (2 ^ (2*n) - 1) ≠
      2 ^ (3*d) * (2 ^ (3*d) - 1) * (2 ^ (2*d) - 1) := by
  intro he
  have hv : 6*n = 3*d := twoPart_eq
    ((odd_pow_sub_one (by omega : 0 < 6*n)).mul (odd_pow_sub_one (by omega : 0 < 2*n)))
    ((odd_pow_sub_one (by omega : 0 < 3*d)).mul (odd_pow_sub_one (by omega : 0 < 2*d)))
    (by simpa only [mul_assoc] using he)
  rw [←hv] at he
  have hc := Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos (by positivity) (Nat.sub_pos_of_lt
      (Nat.one_lt_two_pow (by omega)))) he
  have hp : 2 ^ (2*n) = 2 ^ (2*d) := by
    have h1 := Nat.one_le_two_pow (n := 2*n)
    have h2 := Nat.one_le_two_pow (n := 2*d)
    omega
  have hn' := Nat.pow_right_injective (by decide : 1 < (2:ℕ)) hp
  omega

private theorem linear_two_ne {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    2 ^ (6*n) * (2 ^ (6*n) - 1) * (2 ^ (2*n) - 1) ≠
      2 ^ d * (2 ^ (2*d) - 1) := by
  intro he
  have hv : 6*n = d := twoPart_eq
    ((odd_pow_sub_one (by omega : 0 < 6*n)).mul (odd_pow_sub_one (by omega : 0 < 2*n)))
    (odd_pow_sub_one (by omega : 0 < 2*d))
    (by simpa only [mul_assoc] using he)
  rw [←hv] at he
  have hc := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (6*n))
    (show 2 ^ (6*n) * ((2 ^ (6*n) - 1) * (2 ^ (2*n) - 1)) =
      2 ^ (6*n) * (2 ^ (2*(6*n)) - 1) by simpa only [mul_assoc] using he)
  have ha : 2 ^ (2*n) ≤ 2 ^ (6*n) := Nat.pow_le_pow_right (by decide) (by omega)
  have hb : 1 < 2 ^ (6*n) := Nat.one_lt_two_pow (by omega)
  have hsmall : (2 ^ (6*n) - 1) * (2 ^ (2*n) - 1) ≤ (2 ^ (6*n) - 1)^2 := by
    rw [pow_two]
    gcongr
  have hs := Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ (6*n))
  have hs' := Nat.sub_add_cancel (show 1 ≤ 2 ^ (6*n) * 2 ^ (6*n) by nlinarith)
  rw [show 2*(6*n) = 6*n+6*n by omega, pow_add] at hc
  nlinarith

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

private theorem g2_card :
    Nat.card (Atlas.G2.Model F) =
      2 ^ (6*n) * (2 ^ (6*n) - 1) * (2 ^ (2*n) - 1) := by
  rw [Atlas.G2.card_Model,hc]
  simp only [←pow_mul, Nat.mul_comm n]

/-- The least nonbinary G₂ order exceeds all exceptional small rows. -/
theorem card_g2_ge (hn : 1 < n) :
    251596800 ≤ Nat.card (Atlas.G2.Model F) := by
  have hq : 4 ≤ Nat.card F := by
    rw [hc]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hn
  rw [Atlas.G2.card_Model]
  calc
    251596800 = 4^6 * (4^6-1) * (4^2-1) := by norm_num
    _ ≤ _ := by gcongr

/-- No binary SL₂ natural row has the exceptional quotient order. -/
theorem card_g2_ne_sl_two (hn : 0 < n) (E : BinaryField) :
    Nat.card (Atlas.G2.Model F) ≠ Nat.card SL(2,E.Carrier) := by
  rw [g2_card F hc,Atlas.card_sl_two,E.card_eq]
  simpa only [←pow_mul, Nat.mul_comm E.degree] using linear_two_ne hn E.degree_pos

/-- Neither natural nor doubled-natural SL₃ can be the exceptional row. -/
theorem card_g2_ne_sl_three (hn : 0 < n) (E : BinaryField) :
    Nat.card (Atlas.G2.Model F) ≠ Nat.card SL(3,E.Carrier) := by
  rw [g2_card F hc,card_sl_three,E.card_eq]
  simpa only [←pow_mul, Nat.mul_comm E.degree] using triple_ne hn E.degree_pos

/-- Equality of actual exceptional orders preserves the original field degree. -/
theorem degree_eq_of_card_g2 (hn : 0 < n) (E : BinaryField)
    (he : Nat.card (Atlas.G2.Model F) = Nat.card (Atlas.G2.Model E.Carrier)) :
    E.degree = n := by
  rw [g2_card F hc,g2_card E.Carrier E.card_eq] at he
  have hv := twoPart_eq
    ((odd_pow_sub_one (by omega : 0 < 6*n)).mul (odd_pow_sub_one (by omega : 0 < 2*n)))
    ((odd_pow_sub_one (by have := E.degree_pos; omega : 0 < 6*E.degree)).mul
      (odd_pow_sub_one (by have := E.degree_pos; omega : 0 < 2*E.degree)))
    (by simpa only [mul_assoc] using he)
  omega

/-- The exceptional binary linear rows are smaller than G₂(4). -/
theorem card_g2_ne_binary_higher (hn : 1 < n) {d : ℕ} (hd : d = 4 ∨ d = 5) :
    Nat.card (Atlas.G2.Model F) ≠ Nat.card SL(d,ZMod 2) := by
  have hlo := card_g2_ge F hc hn
  intro he
  rw [he] at hlo
  rcases hd with rfl | rfl <;> rw [binary_card] at hlo <;>
    norm_num [Fin.prod_univ_succ] at hlo

/-- All the small alternating endpoints are below the original nonbinary order. -/
theorem card_g2_ne_alternating (hn : 1 < n) {d : ℕ}
    (hd : d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8) :
    Nat.card (Atlas.G2.Model F) ≠ Nat.card (alternatingGroup (Fin d)) := by
  have hlo := card_g2_ge F hc hn
  intro he
  rw [he] at hlo
  rcases hd with rfl | rfl | rfl | rfl <;>
    rw [nat_card_alternatingGroup] at hlo <;> norm_num [Nat.factorial] at hlo

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear

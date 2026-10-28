module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Exhaustion.LinearDescent
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport
public import BenderSuzuki.External.Huppert.II.theorem_10_12

/-!
# Strict unitary parameter descent from group orders

Transport the actual Hermitian model to the standard form and use the proved
Huppert II.10.12 order formula. A larger unitary exponent gives a larger order
than the ambient PSL₃ group, even after allowing for the scalar kernels.

At equal parameters q, mere size comparison is insufficient. Lagrange's theorem
and the two order formulas instead force q³+1 to divide d(q³−1), where
1 ≤ d ≤ 3. Cancelling the common factors makes this impossible for q ≥ 2.
Thus every actual PSU₃(2^m) subgroup of PSL₃(2^f) has m < f. This argument
needs neither normality, simplicity, nor a representation-classification input.

Sources: Huppert II.10.12, as proved in
`BenderSuzuki/External/Huppert/II/theorem_10_12.lean`; the application is
GLS3, Theorem 6.5.3(g), `refs/KGroup/GLS3/chapter6.tex`.
-/

open CFSG.KnownSimple Matrix Matrix.PSL3.LinearThree
open CFSG.Quasithin.ChapterF.Source.Unitary
open scoped MatrixGroups

namespace CFSG.Quasithin.MainConverse.LinearThreeSections

/-- The actual even unitary model has the classical order, for every allowed Hermitian form. -/
public theorem psu3_even_card_mul {L : Type*} [Group L] {m : ℕ} (hm : 0 < m)
    (hL : ClassicalGroup.IsPSU L 3 (2 ^ m)) :
    Nat.card L * Nat.gcd 3 (2 ^ m + 1) =
      (2 ^ m) ^ 3 * ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 2 - 1) := by
  obtain ⟨E, _, _, J, hcard, hconj, ⟨e⟩⟩ := hL
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J m hm hcard hconj
  let e' := e.trans (FormTransport.projectiveEquiv J C hC)
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ :=
    BenderSuzuki.External.huppert_II_10_12 (FormTransport.standardForm J) (2 ^ m) hcard
      (fixed_card J m hm hcard hconj) rfl
  rw [Nat.card_congr e'.toEquiv, hc]
  have hd2 : Nat.gcd 3 (2 ^ m + 1) ∣ (2 ^ m) ^ 2 - 1 := by
    rw [show (2 ^ m) ^ 2 - 1 = (2 ^ m - 1) * (2 ^ m + 1) from by
      simpa [mul_comm] using Nat.sq_sub_sq (2 ^ m) 1]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
  rw [Nat.div_mul_cancel (dvd_mul_of_dvd_right hd2 _)]
  ring

private theorem unequal_sign_orders {q cL cU : ℕ} (hq : 1 < q)
    (hL : cL * Nat.gcd 3 (q - 1) = q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1))
    (hU : cU * Nat.gcd 3 (q + 1) = q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1)) :
    ¬ cU ∣ cL := by
  rintro ⟨k,hk⟩
  have hq3 : 8 ≤ q ^ 3 := Nat.pow_le_pow_left (show 2 ≤ q by omega) 3
  have hq2 : 4 ≤ q ^ 2 := Nat.pow_le_pow_left (show 2 ≤ q by omega) 2
  have hA : 0 < q ^ 3 * (q ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
  have heq : (q ^ 3 * (q ^ 2 - 1)) * ((q ^ 3 - 1) * Nat.gcd 3 (q + 1)) =
      (q ^ 3 * (q ^ 2 - 1)) * ((q ^ 3 + 1) * (k * Nat.gcd 3 (q - 1))) := by
    calc
      _ = (cL * Nat.gcd 3 (q - 1)) * Nat.gcd 3 (q + 1) := by rw [hL]; ring
      _ = (cU * Nat.gcd 3 (q + 1)) * (k * Nat.gcd 3 (q - 1)) := by rw [hk]; ring
      _ = _ := by rw [hU]; ring
  have he := Nat.eq_of_mul_eq_mul_left hA heq
  let d := Nat.gcd 3 (q + 1)
  let x := k * Nat.gcd 3 (q - 1)
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ (by decide)
  have hd3 : d ≤ 3 := Nat.gcd_le_left _ (by decide)
  have he' : q ^ 3 * d = (q ^ 3 + 1) * x + d := by
    change (q ^ 3 - 1) * d = (q ^ 3 + 1) * x at he
    calc
      q ^ 3 * d = (q ^ 3 - 1 + 1) * d := by rw [Nat.sub_add_cancel (by omega)]
      _ = (q ^ 3 - 1) * d + d := by ring
      _ = _ := by rw [he]
  have hxd : x < d := by
    by_contra hn
    have hh := Nat.mul_le_mul_left (q ^ 3 + 1) (show d ≤ x by omega)
    nlinarith
  have hh := Nat.mul_le_mul_left (q ^ 3) (show x + 1 ≤ d by omega)
  nlinarith

/-- Any injection of an even PSU₃ model into PSL₃ forces a smaller fixed-field exponent. -/
public theorem unitary_parameter_lt_of_injective {f m : ℕ} (hf : 0 < f) (hm : 0 < m)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = 2 ^ f)
    {L : Type*} [Group L] (hL : ClassicalGroup.IsPSU L 3 (2 ^ m))
    (i : L →* PSL(3,F)) (hi : Function.Injective i) : m < f := by
  have hdvd := Subgroup.card_dvd_of_injective i hi
  have hU := psu3_even_card_mul hm hL
  have hL' := card_projective_mul_scalar F
  rw [hF] at hL'
  by_contra hn
  rcases (show f ≤ m by omega).eq_or_lt with hfm | hfm
  · subst m
    exact unequal_sign_orders (Nat.one_lt_two_pow_iff.mpr (by omega)) hL' hU hdvd
  have hg := order_polynomial_growth (Nat.one_lt_two_pow_iff.mpr (by omega : f ≠ 0))
    (show 2 * 2 ^ f ≤ 2 ^ m from by
      rw [mul_comm, ← pow_succ]
      exact Nat.pow_le_pow_right (by decide) hfm)
  have hd1 : 1 ≤ Nat.gcd 3 (2 ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by decide)
  have hd2 : Nat.gcd 3 (2 ^ m + 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
  have hl : Nat.card PSL(3,F) ≤
      (2 ^ f) ^ 3 * ((2 ^ f) ^ 3 - 1) * ((2 ^ f) ^ 2 - 1) := by
    calc
      Nat.card PSL(3,F) ≤ Nat.card PSL(3,F) * Nat.gcd 3 (2 ^ f - 1) :=
        Nat.le_mul_of_pos_right _ hd1
      _ = _ := hL'
  have hr : (2 ^ m) ^ 3 * ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) ≤
      3 * Nat.card L := by
    calc
      _ ≤ (2 ^ m) ^ 3 * ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 2 - 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ = Nat.card L * Nat.gcd 3 (2 ^ m + 1) := hU.symm
      _ ≤ 3 * Nat.card L := by rw [mul_comm]; exact Nat.mul_le_mul_right _ hd2
  have hle := Nat.card_le_card_of_injective i hi
  omega

end CFSG.Quasithin.MainConverse.LinearThreeSections

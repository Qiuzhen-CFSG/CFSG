module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.Models
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Full SL₃ models in the exchanged-component sieve

For a field of order `q = 2^n`, the full SL₃ order is
`q^3 (q^3 - 1) (q^2 - 1)`. Comparing two-parts with an even-field PSL₂
would force its field order to be `q^3`, contradicting the odd parts.
For an odd prime parameter `p`, primality bounds `p` by `q^2 + q + 1`.
The order comparison then forces `q = 2` and `p = 7`.

Field transport gives the actual SL₃(2) model. Only at this binary endpoint
do we pass to PSL₃, using the proved triviality of the scalar center.
These comparisons discharge the SL₃ model intersection; the C.2.7 application
and C.1.34 module arguments remain with the exchanged-component assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.2.7(3)(g),
printed p.145, and the proof of 15.4.20, printed p.1164. The imported scalar
and projective order formulas retain their ATLAS attribution and license.
-/

public section

open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases
variable {Q F : Type*} [Group Q] [Field F] [Finite F]
/-- Equality of the exact two-parts, without any group-theoretic assumptions. -/
private theorem binary_part {a b x y : ℕ} (hx : Odd x) (hy : Odd y)
    (h : 2 ^ a * x = 2 ^ b * y) : a = b := by
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
  have hy0 : y ≠ 0 := by rintro rfl; norm_num at hy
  have hf := congrArg (fun z : ℕ => z.factorization 2) h
  simpa only [Nat.factorization_mul (by positivity : 2 ^ a ≠ 0) hx0,
    Nat.factorization_mul (by positivity : 2 ^ b ≠ 0) hy0,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hx.not_two_dvd_nat,
    Nat.factorization_eq_zero_of_not_dvd hy.not_two_dvd_nat, Finsupp.add_apply, add_zero] using hf

private theorem even_pow_pred_odd {q : ℕ} (hq : 0 < q) (he : Even q)
    {k : ℕ} (hk : k ≠ 0) : Odd (q ^ k - 1) := by
  have he' := he.pow_of_ne_zero hk
  have hp : 0 < q ^ k := pow_pos hq _
  rw [Nat.odd_iff]
  rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero] at he'
  omega

private theorem odd_parameter_bound {q p : ℕ} (hq : 1 < q)
    (hp : p.Prime) (hpq : ¬ p ∣ q)
    (hc : q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) * 2 = p * (p ^ 2 - 1))
    (hp2 : ¬ p ∣ 2) : p ≤ q ^ 2 + q + 1 := by
  have hd : p ∣ q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) * 2 := by
    rw [hc]; exact dvd_mul_right _ _
  have hd' := (hp.dvd_mul.mp hd).resolve_right hp2
  have hf2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [show 1 ≤ q by omega, show 1 ≤ q ^ 2 by nlinarith]
    ring
  have hf3 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    zify [show 1 ≤ q by omega, show 1 ≤ q ^ 3 from Nat.one_le_pow _ _ (by omega)]
    ring
  rcases hp.dvd_mul.mp hd' with hd | hd
  · have hd := (hp.dvd_mul.mp hd).resolve_left (fun h => hpq (hp.dvd_of_dvd_pow h))
    rw [hf3] at hd
    rcases hp.dvd_mul.mp hd with hd | hd
    · exact (Nat.le_of_dvd (by omega) hd).trans (by omega)
    · exact Nat.le_of_dvd (by positivity) hd
  · rw [hf2] at hd
    rcases hp.dvd_mul.mp hd with hd | hd
    · exact (Nat.le_of_dvd (by omega) hd).trans (by omega)
    · exact (Nat.le_of_dvd (by omega) hd).trans (by omega)

/-- The difference of the extremal order polynomials factors as
`q (q-2) (q+1) (q²+q+1) (2q³+q+1)`, and is positive for `q > 2`. -/
private theorem odd_order_forces_two {q p : ℕ} (hq : 1 < q) (hp : 1 < p)
    (hple : p ≤ q ^ 2 + q + 1)
    (hc : q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) * 2 = p * (p ^ 2 - 1)) : q = 2 := by
  have hm := Nat.mul_le_mul hple
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hple 2) 1)
  by_contra hq2
  have hq3 : 2 < q := by omega
  have hqpow3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hqpow2 : 1 ≤ q ^ 2 := by nlinarith
  have hs : 1 ≤ (q ^ 2 + q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  zify [hqpow3, hqpow2, hs, hp2] at hc hm
  have hpos : (0 : ℤ) < (q : ℤ) * (q - 2) * (q + 1) *
      (q ^ 2 + q + 1) * (2 * q ^ 3 + q + 1) := by
    have hq' : (2 : ℤ) < q := by omega
    positivity
  nlinarith only [hc, hm, hpos]
private theorem even_order_impossible {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hc : (2 ^ n) ^ 3 * ((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1) =
      2 ^ m * ((2 ^ m) ^ 2 - 1)) : False := by
  let q := 2 ^ n
  have hq : 1 < q := Nat.one_lt_pow (by omega) (by decide)
  have hqe : Even q := (by decide : Even 2).pow_of_ne_zero (by omega)
  have hme : Even (2 ^ m) := (by decide : Even 2).pow_of_ne_zero (by omega)
  have hodd := (even_pow_pred_odd (by omega : 0 < q) hqe (by decide : 3 ≠ 0)).mul
    (even_pow_pred_odd (by omega : 0 < q) hqe (by decide : 2 ≠ 0))
  have hodd' := even_pow_pred_odd (by positivity : 0 < 2 ^ m) hme (by decide : 2 ≠ 0)
  have hnm : n * 3 = m := binary_part hodd hodd' (by
    simpa only [q, pow_mul, mul_assoc] using hc)
  have hq3 : 1 < q ^ 3 := Nat.one_lt_pow (by decide) hq
  have hmul : q ^ 3 * ((q ^ 3 - 1) * (q ^ 2 - 1)) =
      q ^ 3 * ((q ^ 3) ^ 2 - 1) := by
    simpa only [← hnm, pow_mul, mul_assoc, q] using hc
  have he := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < q ^ 3) hmul
  have hf : (q ^ 3) ^ 2 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
    zify [show 1 ≤ q ^ 3 by omega,
      show 1 ≤ (q ^ 3) ^ 2 from Nat.one_le_pow _ _ (by omega)]
    ring
  rw [hf] at he
  have he' := Nat.eq_of_mul_eq_mul_left (by omega : 0 < q ^ 3 - 1) he
  have hpow : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  omega
private theorem slThree_card :
    Nat.card SL(3, F) = Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(3, F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Matrix.PSL3.LinearThree.card_projective_mul_scalar F

/-- A full even-field SL₃ is never an even-field PSL₂, even without the
swapped model's parity restriction on the PSL₂ exponent. -/
theorem slThree_not_even_psl {n m : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : Q ≃* SL(3, F)) : ¬ ClassicalGroup.IsPSL Q 2 (2 ^ m) := by
  intro he
  have hm : 1 ≤ m := by
    have h := (psl_order he).1
    by_contra hm
    have : m = 0 := by omega
    simp [this] at h
  have hc := even_psl_order he
  rw [Nat.card_congr e.toEquiv, slThree_card, hF] at hc
  exact even_order_impossible hn hm hc

/-- The only odd-prime PSL₂ parameter compatible with a full even-field SL₃
is seven, and the SL₃ field has order two. -/
theorem slThree_odd_prime_parameters {n p : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (e : Q ≃* SL(3, F))
    (hp : p.Prime) (ho : Odd p) (he : ClassicalGroup.IsPSL Q 2 p) : n = 1 ∧ p = 7 := by
  let q := 2 ^ n
  have hq : 1 < q := Nat.one_lt_pow (by omega) (by decide)
  have hg : Nat.gcd 2 (p - 1) = 2 := by
    apply Nat.gcd_eq_left_iff_dvd.mpr
    rw [Nat.dvd_iff_mod_eq_zero]
    rw [Nat.odd_iff] at ho
    omega
  have hc := (psl_order he).2
  rw [Nat.card_congr e.toEquiv, slThree_card, hF, hg] at hc
  change q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) * 2 = p * (p ^ 2 - 1) at hc
  have hp2 : ¬ p ∣ 2 := by
    intro hd
    have : p = 2 := Nat.le_antisymm (Nat.le_of_dvd (by decide) hd) hp.two_le
    norm_num [this] at ho
  have hpq : ¬ p ∣ q := fun hd => hp2 (hp.dvd_of_dvd_pow hd)
  have hple := odd_parameter_bound hq hp hpq hc hp2
  have hq2 := odd_order_forces_two hq hp.one_lt hple hc
  have hn1 : n = 1 := Nat.pow_right_injective (by decide) hq2
  refine ⟨hn1, ?_⟩
  rw [hq2] at hc hple
  norm_num at hc hple
  interval_cases p <;> norm_num at hc
  rfl

/-- The swapped model uses its odd-prime branch with parameter seven. -/
theorem slThree_swapped_parameter {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (e : Q ≃* SL(3, F))
    (hs : Chapter1.XiEmbedding.SwappedModel 3 Q) :
    n = 1 ∧ ClassicalGroup.IsPSL Q 2 7 := by
  rcases hs with ⟨m, _, _, he⟩ | ⟨p, hp, ho, he⟩
  · exact False.elim (slThree_not_even_psl hn hF e he)
  · obtain ⟨hn1, rfl⟩ := slThree_odd_prime_parameters hn hF e hp ho he
    exact ⟨hn1, he⟩

/-- The surviving models are actual SL₃(2), PSL₃(2), and PSL₂(7) models of
the same group; the original field exponent is one. -/
theorem slThree_models_of_swapped {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (e : Q ≃* SL(3, F))
    (hs : Chapter1.XiEmbedding.SwappedModel 3 Q) :
    n = 1 ∧ Nonempty (Q ≃* SL(3, ZMod 2)) ∧
      ClassicalGroup.IsPSL Q 3 2 ∧ ClassicalGroup.IsPSL Q 2 7 := by
  obtain ⟨hn1, hseven⟩ := slThree_swapped_parameter hn hF e hs
  have hc : Nat.card F = 2 := by simpa [hn1] using hF
  let : Fintype F := Fintype.ofFinite F
  let f : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  let ebin : Q ≃* SL(3, ZMod 2) := e.trans (Atlas.fieldEquivSL 3 f.symm)
  have hZ : Subgroup.center SL(3, ZMod 2) = ⊥ :=
    (Matrix.SL3.center_eq_bot_iff_card_mod_three (ZMod 2)).mpr (by norm_num)
  exact ⟨hn1, ⟨ebin⟩, ⟨ZMod 2, inferInstance, inferInstance, by simp,
    ⟨ebin.trans (Matrix.SL3.equivProjectiveOfCenterEqBot (ZMod 2) hZ)⟩⟩, hseven⟩
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases

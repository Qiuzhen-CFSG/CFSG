module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.Remaining
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.OrderRestrictions
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum.PointRestrictions
import Mathlib.GroupTheory.GroupAction.Period

/-!
# The odd-order spectrum of native M₂₄

The actual Witt-design action gives a short structural reduction. Every odd-prime
subgroup fixes at most six points. Thus the prime-order powers belonging to any
two distinct odd prime divisors of an element order have overlapping supports.
At a point in the intersection their commuting product has period `p * q`, so
`p * q ≤ 24`. This excludes all pairs except `3 * 5` and `3 * 7`.

The native group order, oddness, and the exponent-three Sylow subgroup reduce
the element order to a divisor of `3 * 5 * 7 * 11 * 23`. Splitting those five
prime factors proves coverage by thirty-two elementary cases. No permutation
partition enumeration or assumed class table is used.

This supplies the `OddOrderSpectrum` input to the degree-eleven trace-field
calculation. Source application: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 5.1, M₂₄ paragraph, manuscript p.17
(https://agag-malle.math.rptu.de/~malle/download/failfact.dvi).
-/

public section

namespace Sporadic.Mathieu.M24OddCyclic

/-- Every odd-prime element moves at least eighteen of the twenty-four points. -/
private theorem prime_support (g : M24) {p : ℕ} (hp : p.Prime)
    (ho : Odd p) (hg : orderOf g = p) : 18 ≤ g.val.support.card := by
  classical
  have hfix : MulAction.fixedPoints (Subgroup.zpowers g) (Fin 24) =
      Function.fixedPoints g.val := by
    ext i
    constructor
    · intro hi
      exact hi ⟨g, Subgroup.mem_zpowers g⟩
    · intro hi a
      exact smul_eq_self_of_mem_zpowers a.property hi
  have hr := MathieuCode.m24_odd_prime_point_restriction (Subgroup.zpowers g)
    hp ho ((Nat.card_zpowers g).trans hg)
  rw [hfix] at hr
  have hf : Nat.card (Function.fixedPoints g.val) + g.val.support.card = 24 := by
    rw [Nat.card_eq_fintype_card, Equiv.Perm.card_fixedPoints,
      Equiv.Perm.sum_cycleType, Fintype.card_fin]
    exact Nat.sub_add_cancel (Finset.card_le_univ g.val.support)
  rcases hr with ⟨_, h | h⟩ | ⟨_, h⟩ <;> omega

private theorem prime_period (a : Equiv.Perm (Fin 24)) {p : ℕ}
    (hp : p.Prime) (ha : orderOf a = p) (i : Fin 24) (hi : a i ≠ i) :
    Function.minimalPeriod a i = p := by
  let : Fact p.Prime := ⟨hp⟩
  apply Function.minimalPeriod_eq_prime
  · change (a ^ p) i = i
    rw [← ha, pow_orderOf_eq_one]
    rfl
  · exact hi

/-- Overlapping supports of commuting prime-order powers force a period of length `p * q`. -/
private theorem prime_pair_bound (g : M24) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hop : Odd p) (hoq : Odd q)
    (hpq : p ≠ q) (hpd : p ∣ orderOf g) (hqd : q ∣ orderOf g) : p * q ≤ 24 := by
  classical
  let a := g ^ (orderOf g / p)
  let b := g ^ (orderOf g / q)
  have ha : orderOf a = p := orderOf_pow_orderOf_div (orderOf_pos g).ne' hpd
  have hb : orderOf b = q := orderOf_pow_orderOf_div (orderOf_pos g).ne' hqd
  have has := prime_support a hp hop ha
  have hbs := prime_support b hq hoq hb
  have hi : (a.val.support ∩ b.val.support).Nonempty := by
    have hc := Finset.card_union_add_card_inter a.val.support b.val.support
    have hu := Finset.card_le_univ (a.val.support ∪ b.val.support)
    have hn : 0 < (a.val.support ∩ b.val.support).card := by
      simp only [Fintype.card_fin] at hu
      omega
    exact Finset.card_pos.mp hn
  obtain ⟨i, hi⟩ := hi
  obtain ⟨hai, hbi⟩ := Finset.mem_inter.mp hi
  have hap : Function.minimalPeriod a.val i = p :=
    prime_period a.val hp (by simpa using ha) i (Equiv.Perm.mem_support.mp hai)
  have hbp : Function.minimalPeriod b.val i = q :=
    prime_period b.val hq (by simpa using hb) i (Equiv.Perm.mem_support.mp hbi)
  have hc : Function.Commute a.val b.val := by
    intro x
    exact congrArg (fun z : M24 => z.val x)
      (Commute.pow_pow_self g (orderOf g / p) (orderOf g / q)).eq
  have hcop : Nat.Coprime (Function.minimalPeriod a.val i)
      (Function.minimalPeriod b.val i) := by
    rw [hap, hbp]
    exact hp.coprime_iff_not_dvd.mpr
      (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
  have he := hc.minimalPeriod_of_comp_eq_mul_of_coprime hcop
  have hl := Function.minimalPeriod_le_card (f := a.val ∘ b.val) (x := i)
  rw [he, hap, hbp] at hl
  exact hl

/-- Oddness removes the two-part, and exclusion of nine removes the repeated three-factors. -/
private theorem odd_order_dvd (n : ℕ) (hd : n ∣ 244823040)
    (h2 : ¬ 2 ∣ n) (h9 : ¬ 9 ∣ n) : n ∣ 3 * 5 * 7 * 11 * 23 := by
  have ho : n ∣ 3 ^ 3 * (5 * 7 * 11 * 23) := by
    apply ((Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm.pow_right 10).dvd_of_dvd_mul_left
    norm_num
    exact hd
  obtain ⟨a, b, ha, hb, hab⟩ := Nat.dvd_mul.mp ho
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp ha
  have hk2 : k < 2 := by
    by_contra hn
    apply h9
    rw [← hab]
    exact dvd_mul_of_dvd_left (show 3 ^ 2 ∣ 3 ^ k from pow_dvd_pow 3 (by omega)) b
  interval_cases k <;> norm_num at hab <;> subst n
  · exact dvd_mul_of_dvd_right hb 3
  · exact Nat.mul_dvd_mul_left 3 hb

/-- The five prime factors give only thirty-two divisors; the eight large pairs are excluded. -/
private theorem arithmetic_spectrum (n : ℕ) (hd : n ∣ 3 * 5 * 7 * 11 * 23)
    (h33 : ¬ 33 ∣ n) (h35 : ¬ 35 ∣ n) (h55 : ¬ 55 ∣ n) (h77 : ¬ 77 ∣ n)
    (h69 : ¬ 69 ∣ n) (h115 : ¬ 115 ∣ n) (h161 : ¬ 161 ∣ n) (h253 : ¬ 253 ∣ n) :
    n = 1 ∨ n.Prime ∨ n = 15 ∨ n = 21 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.mp hd
  obtain ⟨c, d, hc, hd11, rfl⟩ := Nat.dvd_mul.mp ha
  obtain ⟨e, f, he, hf, rfl⟩ := Nat.dvd_mul.mp hc
  obtain ⟨i, j, hi, hj, rfl⟩ := Nat.dvd_mul.mp he
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hi with rfl | rfl <;>
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hj with rfl | rfl <;>
    rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hf with rfl | rfl <;>
    rcases (Nat.dvd_prime (by decide : Nat.Prime 11)).mp hd11 with rfl | rfl <;>
    rcases (Nat.dvd_prime (by decide : Nat.Prime 23)).mp hb with rfl | rfl <;>
    norm_num at *
  all_goals decide

private theorem prime_pair_not_dvd (g : M24) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hop : Odd p) (hoq : Odd q)
    (hpq : p ≠ q) (hlarge : 24 < p * q) : ¬ p * q ∣ orderOf g := by
  intro hd
  have hpd : p ∣ orderOf g := (dvd_mul_right p q).trans hd
  have hqd : q ∣ orderOf g := (dvd_mul_left q p).trans hd
  exact (prime_pair_bound g hp hq hop hoq hpq hpd hqd).not_gt hlarge

/-- The odd-order spectrum of the native Witt-design M₂₄ carrier. -/
theorem oddOrderSpectrum : OddOrderSpectrum := by
  intro g hg
  have hd : orderOf g ∣ 244823040 := by
    simpa only [m24_order] using orderOf_dvd_natCard g
  have hr := odd_order_dvd (orderOf g) hd hg (nine_not_dvd_orderOf g)
  apply arithmetic_spectrum (orderOf g) hr
  · exact prime_pair_not_dvd g (p := 3) (q := 11) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact prime_pair_not_dvd g (p := 5) (q := 7) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact prime_pair_not_dvd g (p := 5) (q := 11) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact prime_pair_not_dvd g (p := 7) (q := 11) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact prime_pair_not_dvd g (p := 3) (q := 23) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact prime_pair_not_dvd g (p := 5) (q := 23) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact prime_pair_not_dvd g (p := 7) (q := 23) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact prime_pair_not_dvd g (p := 11) (q := 23) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

end Sporadic.Mathieu.M24OddCyclic

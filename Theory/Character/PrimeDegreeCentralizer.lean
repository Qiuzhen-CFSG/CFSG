module

public import Theory.Character.VanishingCentralizer
public import Theory.Character.CharacterKernel
public import Theory.Character.Integrality
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith

/-!
# Self-centralization from rational prime-degree characters

Let `P` be a Sylow subgroup of prime order `p` with odd centralizer. A faithful
complex representation of dimension `p`, with rational character values and
vanishing on all `p`-singular elements, forces `C_G(P) = P`.

Here is an elementary alternative to the central-complement restriction
argument. Suppose an element `y` of prime order `q ≠ p` centralizes `P`, and
choose `x ∈ P` of order `p`. Rationality and algebraic integrality make the
character value at `y` an integer `a`. Since the value at `xy` vanishes, the
commuting-element character congruence gives `p ∣ a`. The trace bound gives
`-p ≤ a ≤ p`, so `a` is `-p`, `0`, or `p`. The prime-order trace congruence
`a ≡ p (mod q)` excludes the first two possibilities because `q` is odd and
distinct from `p`. The last possibility puts `y` in the representation kernel,
contradicting faithfulness. Cauchy's theorem now makes the centralizer a
`p`-group, and Sylow maximality gives equality.

No rational realization or irreducibility is assumed. A separate oddness
hypothesis on `p` is unnecessary: oddness of the centralizer suffices.

Source: Alperin--Brauer--Gorenstein, III.8 Proposition 5, article p.117,
the self-centralization argument in Cases I and II. The congruence route uses
Peterfalvi (1.10), via `Theory.Character.VanishingCentralizer`, and the
finite-order trace bounds and congruence in `Theory.Character.FiniteOrderTrace`.
-/

namespace Representation

/-- Any odd prime-order element commuting with an element of order `p` has order `p`.
The integer trace is a multiple of `p` between `-p` and `p`; its congruence modulo
its own prime order and faithfulness eliminate all three possibilities otherwise. -/
private theorem prime_order_eq_of_commuting_prime_degree
    {G : Type*} [Group G] [Finite G] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqodd : Odd q) (ρ : Representation ℂ G (Fin p → ℂ))
    (hfaith : Function.Injective ρ)
    (hrat : ∀ g, ∃ r : ℚ, ρ.character g = (r : ℂ))
    (hv : ∀ g, p ∣ orderOf g → ρ.character g = 0)
    {x y : G} (hx : orderOf x = p) (hy : orderOf y = q)
    (hc : Commute x y) : q = p := by
  classical
  by_contra hqp
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨a, ha⟩ := (character_value_isIntegral ρ y).exists_int_iff_exists_rat.mp (hrat y)
  have hcop : (orderOf x).Coprime (orderOf y) := by
    rw [hx, hy]
    exact hp.coprime_iff_not_dvd.mpr
      (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp h).symm)
  have hxy : p ∣ orderOf (x * y) := by
    rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hx]
    exact dvd_mul_right _ _
  obtain ⟨k, hk⟩ := ρ.prime_dvd_integer_character_of_commuting_zero hp hx hc a ha
    (hv _ hxy)
  have hpow : (ρ y) ^ q = 1 := by rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
  have habs : |(a : ℝ)| ≤ (p : ℝ) := by
    calc
      |(a : ℝ)| = |(ρ.character y).re| := by rw [ha]; simp
      _ ≤ ‖ρ.character y‖ := Complex.abs_re_le_norm _
      _ ≤ (p : ℝ) := by
        simpa [Representation.character] using
          finite_order_end_norm_trace_le_finrank (ρ y) hq.ne_zero hpow
  have hlo : -(p : ℤ) ≤ a := by exact_mod_cast (abs_le.mp habs).1
  have hhi : a ≤ (p : ℤ) := by exact_mod_cast (abs_le.mp habs).2
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hklo : -1 ≤ k := by nlinarith only [hlo, hk, hpz]
  have hkhi : k ≤ 1 := by nlinarith only [hhi, hk, hpz]
  have hcong : (q : ℤ) ∣ a - (p : ℤ) := by
    simpa using prime_dvd_integer_trace_sub_finrank (ρ y) hq hpow a ha
  interval_cases k
  · have ha' : a = -(p : ℤ) := by nlinarith only [hk]
    have hd : (q : ℤ) ∣ -((2 * p : ℕ) : ℤ) := by
      convert hcong using 1
      push_cast
      omega
    have hd' : q ∣ 2 * p := by exact_mod_cast (dvd_neg.mp hd)
    rcases hq.dvd_mul.mp hd' with hd2 | hdp
    · have heq := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hd2
      rw [heq] at hqodd
      exact hqodd.not_two_dvd_nat (dvd_refl 2)
    · exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdp)
  · have ha' : a = 0 := by simpa using hk
    rw [ha', zero_sub] at hcong
    have hd : q ∣ p := by exact_mod_cast (dvd_neg.mp hcong)
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd)
  · have ha' : a = (p : ℤ) := by simpa using hk
    have hker : y ∈ ρ.ker := (ρ.mem_ker_iff_character_eq_degree y).mpr (by
      rw [ha, ha', char_one]
      simp)
    have hyone : y = 1 := hfaith (by simpa using hker)
    have : q = 1 := by simpa [hyone] using hy.symm
    exact hq.ne_one this

/-- A faithful rational-valued representation of prime degree, vanishing on
all elements of order divisible by that prime, makes a prime-order Sylow subgroup
self-centralizing whenever its centralizer has odd order. -/
public theorem centralizer_sylow_eq_of_faithful_rational_prime_degree
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : Nat.card P = p)
    (hodd : Odd (Nat.card (Subgroup.centralizer (P : Set G))))
    (ρ : Representation ℂ G (Fin p → ℂ))
    (hfaith : Function.Injective ρ)
    (hrat : ∀ g, ∃ q : ℚ, ρ.character g = (q : ℂ))
    (hv : ∀ g, p ∣ orderOf g → ρ.character g = 0) :
    Subgroup.centralizer (P : Set G) = (P : Subgroup G) := by
  classical
  have hp : p.Prime := Fact.out
  let C := Subgroup.centralizer (P : Set G)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) p (by rw [hP])
  have hxG : orderOf (x : G) = p := (Subgroup.orderOf_coe x).trans hx
  have hprime : ∀ q : ℕ, q.Prime → q ∣ Nat.card C → q = p := by
    intro q hq hqd
    let : Fact q.Prime := ⟨hq⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := C) q hqd
    have hqodd : Odd q := hodd.of_dvd_nat hqd
    apply prime_order_eq_of_commuting_prime_degree hp hq hqodd ρ hfaith hrat hv
      hxG ((Subgroup.orderOf_coe y).trans hy)
    exact Subgroup.mem_centralizer_iff.mp y.property x x.property
  have hC : IsPGroup p C := by
    apply IsPGroup.of_card_dvd_pow (n := Nat.card C)
    apply (Nat.dvd_pow_self_iff (Nat.card_pos (α := C)).ne' hp.ne_zero).mpr
    intro q hq
    obtain ⟨hqprime, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    rw [hprime q hqprime hqd]
    exact Nat.mem_primeFactors.mpr ⟨hp, dvd_refl p, hp.ne_zero⟩
  apply P.is_maximal' hC
  let : IsCyclic P := isCyclic_of_prime_card hP
  exact Subgroup.le_centralizer (P : Subgroup G)

end Representation

module

public import Theory.Character.SchurDegreeSeven
public import Theory.Character.DefectZeroVanishing
public import Theory.Character.VanishingCentralizer

/-!
# Self-centralizing seven-subgroups in Fong's degree-seven argument

A rational-valued irreducible character of degree seven, with value minus one
on involutions, forces every subgroup of order seven to be self-centralizing
when the Sylow two-subgroups have order 32 and the ambient group is simple.

Schur's bound makes the Sylow seven order divide seven, so ordinary defect-zero
vanishing applies. The mixed commuting-element congruence then excludes
centralizing elements of orders two, three, and five: their integer character
values are not divisible by seven. In particular all three order-three values
4, 1, and -2 are retained. Cauchy's theorem excludes these prime divisors from
the centralizer order, and Schur's bound leaves only a divisor of seven.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), printed p.74. The character is supplied explicitly;
its construction and the subsequent group-order reduction belong to consumers.
-/

namespace Stellmacher.Recognition.FongWreathed

private theorem sylow_seven_card_dvd
    {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G ∣ 2^5 * 3^4 * 5 * 7) (P : Sylow 7 G) :
    Nat.card P ∣ 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hd := P.1.card_subgroup_dvd_card.trans hG
  obtain ⟨e, he⟩ := P.isPGroup'.exists_card_eq
  have hc : (Nat.card P).Coprime (2^5 * 3^4 * 5) := by
    rw [he]
    exact (by decide : Nat.Coprime 7 (2^5 * 3^4 * 5)).pow_left e
  exact hc.dvd_of_dvd_mul_left hd

private theorem prime_not_dvd_centralizer_seven
    {G : Type*} [Group G] [Finite G] {χ : ClassFunction G}
    (hχ : IsCharacter χ) (hv : ∀ g, 7 ∣ orderOf g → χ g = 0)
    {t : G} (ht : orderOf t = 7) {p : ℕ} (hp : p.Prime)
    (hvalue : ∀ u : G, orderOf u = p →
      ∃ a : ℤ, χ u = (a : ℂ) ∧ ¬ (7 : ℤ) ∣ a) :
    ¬ p ∣ Nat.card (Subgroup.centralizer (Subgroup.zpowers t : Set G)) := by
  intro hd
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.centralizer (Subgroup.zpowers t : Set G)) p hd
  obtain ⟨a, ha, hna⟩ := hvalue u ((Subgroup.orderOf_coe u).trans hu)
  have hc := hχ.prime_not_dvd_centralizer_card_of_vanishing
    (by decide : Nat.Prime 7) hv (u : G) a ha hna
  have htmem : t ∈ Subgroup.centralizer ({(u : G)} : Set G) := by
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (u.property t (Subgroup.mem_zpowers t))
  apply hc
  simpa only [← Subgroup.orderOf_coe, ht] using (orderOf_dvd_natCard
    (⟨t, htmem⟩ : Subgroup.centralizer ({(u : G)} : Set G)))

/-- Fong's degree-seven character makes each cyclic subgroup of order seven
self-centralizing. -/
public theorem centralizer_zpowers_eq_of_degree_seven
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Nat.card S = 32) {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    (hrat : ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ))
    (hinv : ∀ u : G, orderOf u = 2 → χ u = -1)
    {t : G} (ht : orderOf t = 7) :
    Subgroup.centralizer (Subgroup.zpowers t : Set G) = Subgroup.zpowers t := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hG := hχ.card_dvd_degree_seven_bound S hS hdegree hrat
  let P : Sylow 7 G := Classical.choice inferInstance
  have hv : ∀ g : G, 7 ∣ orderOf g → χ g = 0 :=
    OrdinaryCharacter.value_eq_zero_of_sylow_card_dvd_degree P hχ hdegree
      (sylow_seven_card_dvd hG P)
  have hchar : IsCharacter χ := by
    obtain ⟨n, ρ, _, hρ⟩ := hχ
    exact ⟨n, ρ, hρ⟩
  let C := Subgroup.centralizer (Subgroup.zpowers t : Set G)
  have h2 : ¬ 2 ∣ Nat.card C := by
    apply prime_not_dvd_centralizer_seven hchar hv ht (by decide)
    intro u hu
    exact ⟨-1, by simpa using hinv u hu, by norm_num⟩
  have h3 : ¬ 3 ∣ Nat.card C := by
    apply prime_not_dvd_centralizer_seven hchar hv ht (by decide)
    intro u hu
    rcases hχ.degree_seven_value_of_order_three hdegree hu (hrat u) with h | h | h
    · exact ⟨4, by simpa using h, by norm_num⟩
    · exact ⟨1, by simpa using h, by norm_num⟩
    · exact ⟨-2, by simpa using h, by norm_num⟩
  have h5 : ¬ 5 ∣ Nat.card C := by
    apply prime_not_dvd_centralizer_seven hchar hv ht (by decide)
    intro u hu
    exact ⟨2, by simpa using hχ.degree_seven_value_of_order_five hdegree hu (hrat u),
      by norm_num⟩
  have hcop : (Nat.card C).Coprime (2^5 * 3^4 * 5) := by
    exact ((Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm.pow_right 5).mul_right
      (((Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm.pow_right 4)) |>.mul_right
      ((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr h5).symm
  have hC : Nat.card C ∣ 7 :=
    hcop.dvd_of_dvd_mul_left (C.card_subgroup_dvd_card.trans hG)
  apply (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers t).le_centralizer ?_).symm
  rw [Nat.card_zpowers, ht]
  exact Nat.le_of_dvd (by decide) hC

/-- The equivalent element-centralizer form of the degree-seven result. -/
public theorem centralizer_eq_zpowers_of_degree_seven
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Nat.card S = 32) {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    (hrat : ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ))
    (hinv : ∀ u : G, orderOf u = 2 → χ u = -1)
    {t : G} (ht : orderOf t = 7) :
    Subgroup.centralizer ({t} : Set G) = Subgroup.zpowers t := by
  have h := centralizer_zpowers_eq_of_degree_seven S hS hχ hdegree hrat hinv ht
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    ← Subgroup.zpowers_eq_closure] at h

end Stellmacher.Recognition.FongWreathed

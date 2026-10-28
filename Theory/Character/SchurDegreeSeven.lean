module

public import Theory.Character.SchurDegreeTwelve

/-!
# Schur's rational-character bound in degree seven

A rational-valued irreducible character of degree seven of a finite simple
group is faithful. Schur's factorial bound on each odd Sylow subgroup gives
the prime-power bounds `3^4`, `5`, and `7`; no larger odd prime occurs. With
a Sylow two-subgroup of order 32 this bounds the group order by divisibility
into `2^5 * 3^4 * 5 * 7`.

Schur's prime-power trace spacing also gives the values 2 at order five,
0 at order seven, and 4, 1, or -2 at order three. The last possibility is
retained: excluding it requires additional hypotheses. The character is an
explicit input and no rational realization is assumed.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), printed pp. 74–75. Schur's bound and trace spacing are supplied
by `SchurDegreeTwelve` and `PrimePowerTrace`.
-/

/-- A degree-seven irreducible character of a finite simple group is afforded
by a faithful complex representation of dimension seven. -/
public theorem IsIrreducibleCharacter.exists_faithful_degree_seven
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7) :
    ∃ ρ : Representation ℂ G (Fin 7 → ℂ), χ = ρ.character ∧ Function.Injective ρ := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  have hn : n = 7 := by
    have heq : (n : ℂ) = 7 := by simpa using hdegree
    exact_mod_cast heq
  subst n
  let : Representation.IsIrreducible ρ := hρ
  exact ⟨ρ, rfl, ρ.injective_of_isSimpleGroup_of_one_lt_finrank (by simp)⟩

/-- Extract the odd prime-power part of the degree-seven factorial bound. -/
public theorem prime_pow_dvd_degree_seven_bound
    (p e : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (h : p ^ e ∣ p ^ (7 / (p - 1)) * (7 / (p - 1)).factorial) :
    p ^ e ∣ 2^5 * 3^4 * 5 * 7 := by
  by_cases hlarge : 8 < p
  · have hk : 7 / (p - 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp only [hk, pow_zero, Nat.factorial_zero, mul_one] at h
    exact h.trans (one_dvd _)
  have hsmall : p ≤ 8 := by omega
  have hcases : p = 3 ∨ p = 5 ∨ p = 7 := by
    interval_cases p <;> norm_num at hp <;> norm_num
    omega
  rcases hcases with rfl | rfl | rfl
  · norm_num at h
    have hc : (3 ^ e).Coprime 2 := (by decide : Nat.Coprime 3 2).pow_left e
    have hd : 3 ^ e ∣ 81 := hc.dvd_mul_right.mp (by simpa using h)
    exact hd.trans (by norm_num)
  · norm_num at h
    exact h.trans (by norm_num)
  · norm_num at h
    exact h.trans (by norm_num)

/-- Assemble the numerical bound from the odd Sylow bounds and a Sylow
two-subgroup of order 32. -/
public theorem card_dvd_degree_seven_bound_of_sylow_bounds
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (hS : Nat.card S = 32)
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p G,
      Nat.card P ∣ p ^ (7 / (p - 1)) * (7 / (p - 1)).factorial) :
    Nat.card G ∣ 2^5 * 3^4 * 5 * 7 := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p e hp he
  let : Fact p.Prime := ⟨hp⟩
  by_cases htwo : p = 2
  · subst p
    have hd := S.pow_dvd_card_of_pow_dvd_card he
    rw [hS] at hd
    exact hd.trans (by norm_num)
  · let P : Sylow p G := Classical.choice inferInstance
    apply prime_pow_dvd_degree_seven_bound p e hp htwo
    exact (P.pow_dvd_card_of_pow_dvd_card he).trans (hodd p htwo P)

/-- A finite simple group with a rational-valued irreducible character of
degree seven and a Sylow two-subgroup of order 32 satisfies Schur's bound.
The factor `2^5` comes from the Sylow hypothesis. -/
public theorem IsIrreducibleCharacter.card_dvd_degree_seven_bound
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Nat.card S = 32) {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    (hrat : ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ)) :
    Nat.card G ∣ 2^5 * 3^4 * 5 * 7 := by
  obtain ⟨ρ, rfl, hfaithful⟩ := hχ.exists_faithful_degree_seven hdegree
  apply card_dvd_degree_seven_bound_of_sylow_bounds S hS
  intro p hp _ P
  exact ρ.sylow_card_dvd_pow_mul_factorial_of_rational_character hfaithful hrat P

private theorem degree_seven_prime_order_spacing
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    {g : G} {p : ℕ} (hp : p.Prime) (hg : orderOf g = p)
    (hrat : ∃ q : ℚ, χ g = (q : ℂ)) :
    ∃ j : ℕ, j < 7 / (p - 1) ∧ χ g = 7 - (p : ℂ) * (j + 1) := by
  obtain ⟨ρ, rfl, hfaithful⟩ := hχ.exists_faithful_degree_seven hdegree
  have hpow : (ρ g) ^ (p ^ 1) = 1 := by
    rw [pow_one, ← map_pow, ← hg, pow_orderOf_eq_one, map_one]
  have hne : ρ g ≠ 1 := by
    intro h
    have hg1 : g = 1 := hfaithful (h.trans (map_one ρ).symm)
    have hp1 : p = 1 := by simpa [hg1] using hg.symm
    exact hp.ne_one hp1
  simpa only [Representation.character, Module.finrank_pi, Module.finrank_self,
    Fintype.card_fin, mul_one, Nat.cast_ofNat] using
    prime_power_trace_spacing_of_rational (ρ g) hp hpow hne hrat

/-- At order five, a rational-valued degree-seven irreducible character of a
finite simple group has value two. Rationality at this element suffices. -/
public theorem IsIrreducibleCharacter.degree_seven_value_of_order_five
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    {g : G} (hg : orderOf g = 5) (hrat : ∃ q : ℚ, χ g = (q : ℂ)) : χ g = 2 := by
  obtain ⟨j, hj, hvalue⟩ := degree_seven_prime_order_spacing hχ hdegree (by decide) hg hrat
  have hj0 : j = 0 := by norm_num at hj; omega
  norm_num [hj0] at hvalue
  exact hvalue

/-- At order three, the possible rational values in degree seven are four,
one, and minus two. The trace-spacing argument alone does not exclude minus two. -/
public theorem IsIrreducibleCharacter.degree_seven_value_of_order_three
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    {g : G} (hg : orderOf g = 3) (hrat : ∃ q : ℚ, χ g = (q : ℂ)) :
    χ g = 4 ∨ χ g = 1 ∨ χ g = -2 := by
  obtain ⟨j, hj, hvalue⟩ := degree_seven_prime_order_spacing hχ hdegree (by decide) hg hrat
  norm_num at hj
  interval_cases j <;> norm_num at hvalue ⊢ <;> simp [hvalue]

/-- At order seven, a rational-valued degree-seven irreducible character of a
finite simple group vanishes. Rationality at this element suffices. -/
public theorem IsIrreducibleCharacter.degree_seven_value_of_order_seven
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 7)
    {g : G} (hg : orderOf g = 7) (hrat : ∃ q : ℚ, χ g = (q : ℂ)) : χ g = 0 := by
  obtain ⟨j, hj, hvalue⟩ := degree_seven_prime_order_spacing hχ hdegree (by decide) hg hrat
  have hj0 : j = 0 := by norm_num at hj; omega
  norm_num [hj0] at hvalue
  exact hvalue

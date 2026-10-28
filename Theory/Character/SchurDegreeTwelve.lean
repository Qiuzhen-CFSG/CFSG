module

public import Theory.Character.Blichfeldt
public import Theory.Character.PrimePowerTrace
public import Theory.Character.SimpleFaithful
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Prime

/-!
# Schur's rational-character bound in degree twelve

For an odd prime `p`, the rational-character argument bounds the Sylow order
by `p ^ k * k!`, where `k = 12 / (p - 1)`. The prime-power part of this bound
is respectively `3^8`, `5^3`, `7^2`, `11`, and `13`; larger primes do not occur.
The power of two is supplied separately by the actual Sylow order.

For a faithful complex representation of a p-group, rational traces lie in
Schur's list of evenly spaced values. Blichfeldt's character-polynomial
divisibility then gives the factorial bound. Restriction to Sylow subgroups
and faithfulness of nonlinear irreducible characters of simple groups give
the final corollary. Rational-valued characters are never assumed to have a
rational realization.

Source: Schur, *Über eine Klasse von endlichen Gruppen linearen
Substitutionen* (1905), pp. 77–91; the numerical specialization is used in
Lyons, *A Characterization of the Group U₃(4)*, §5, p. 386.
-/

/-- Schur's factorial bound for a faithful rational-valued complex
representation of a finite p-group. -/
public theorem Representation.card_dvd_pow_mul_factorial_of_isPGroup
    {G : Type*} [Group G] [Finite G] {n p : ℕ} (hp : p.Prime)
    (hG : IsPGroup p G) (ρ : Representation ℂ G (Fin n → ℂ))
    (hfaithful : Function.Injective ρ)
    (hrat : ∀ g : G, ∃ q : ℚ, ρ.character g = (q : ℂ)) :
    Nat.card G ∣ p ^ (n / (p - 1)) * (n / (p - 1)).factorial := by
  have hχ : IsCharacter ρ.character := ⟨n, ρ, rfl⟩
  apply hχ.card_dvd_pow_mul_factorial_of_values n p (n / (p - 1)) (by simp)
  intro g hg
  obtain ⟨a, ha⟩ := hG.exists_pow_pow_eq_one g
  have hpow : (ρ g) ^ (p ^ a) = 1 := by rw [← map_pow, ha, map_one]
  have hne : ρ g ≠ 1 := fun h => hg (hfaithful (h.trans (map_one ρ).symm))
  simpa only [Representation.character, Module.finrank_pi, Module.finrank_self,
    Fintype.card_fin, mul_one] using
    prime_power_trace_spacing_of_rational (ρ g) hp hpow hne (hrat g)

/-- Every Sylow subgroup of a group with a faithful rational-valued complex
representation satisfies Schur's factorial bound. -/
public theorem Representation.sylow_card_dvd_pow_mul_factorial_of_rational_character
    {G : Type*} [Group G] [Finite G] {n p : ℕ} [Fact p.Prime]
    (ρ : Representation ℂ G (Fin n → ℂ)) (hfaithful : Function.Injective ρ)
    (hrat : ∀ g : G, ∃ q : ℚ, ρ.character g = (q : ℂ)) (P : Sylow p G) :
    Nat.card P ∣ p ^ (n / (p - 1)) * (n / (p - 1)).factorial := by
  exact Representation.card_dvd_pow_mul_factorial_of_isPGroup
    Fact.out P.isPGroup' (ρ.comp P.toSubgroup.subtype)
    (hfaithful.comp Subtype.val_injective) (fun g => hrat g)

/-- A degree-twelve irreducible character of a finite simple group is afforded
by a faithful complex representation of dimension twelve. -/
public theorem IsIrreducibleCharacter.exists_faithful_degree_twelve
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 12) :
    ∃ ρ : Representation ℂ G (Fin 12 → ℂ), χ = ρ.character ∧ Function.Injective ρ := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  have hn : n = 12 := by
    have heq : (n : ℂ) = 12 := by simpa using hdegree
    exact_mod_cast heq
  subst n
  let : Representation.IsIrreducible ρ := hρ
  exact ⟨ρ, rfl, ρ.injective_of_isSimpleGroup_of_one_lt_finrank (by simp)⟩

/-- Extract the odd prime-power part of the degree-twelve factorial bound. -/
public theorem prime_pow_dvd_degree_twelve_bound
    (p e : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (h : p ^ e ∣ p ^ (12 / (p - 1)) * (12 / (p - 1)).factorial) :
    p ^ e ∣ 2^6 * 3^8 * 5^3 * 7^2 * 11 * 13 := by
  by_cases hlarge : 13 < p
  · have hk : 12 / (p - 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp only [hk, pow_zero, Nat.factorial_zero, mul_one] at h
    exact h.trans (one_dvd _)
  have hsmall : p ≤ 13 := by omega
  have hcases : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
    interval_cases p <;> norm_num at hp <;> norm_num
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · norm_num at h
    have hc : (3 ^ e).Coprime 80 := (by decide : Nat.Coprime 3 80).pow_left e
    have hd : 3 ^ e ∣ 6561 := hc.dvd_mul_right.mp (by simpa using h)
    exact hd.trans (by norm_num)
  · norm_num at h
    have hc : (5 ^ e).Coprime 6 := (by decide : Nat.Coprime 5 6).pow_left e
    have hd : 5 ^ e ∣ 125 := hc.dvd_mul_right.mp (by simpa using h)
    exact hd.trans (by norm_num)
  · norm_num at h
    have hc : (7 ^ e).Coprime 2 := (by decide : Nat.Coprime 7 2).pow_left e
    have hd : 7 ^ e ∣ 49 := hc.dvd_mul_right.mp (by simpa using h)
    exact hd.trans (by norm_num)
  · norm_num at h
    exact h.trans (by norm_num)
  · norm_num at h
    exact h.trans (by norm_num)

/-- Assemble the numerical bound from the odd Sylow bounds and a Sylow
two-subgroup of order 64. -/
public theorem card_dvd_degree_twelve_bound_of_sylow_bounds
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (hS : Nat.card S = 64)
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p G,
      Nat.card P ∣ p ^ (12 / (p - 1)) * (12 / (p - 1)).factorial) :
    Nat.card G ∣ 2^6 * 3^8 * 5^3 * 7^2 * 11 * 13 := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p e hp he
  let : Fact p.Prime := ⟨hp⟩
  by_cases htwo : p = 2
  · subst p
    have hd := S.pow_dvd_card_of_pow_dvd_card he
    rw [hS] at hd
    exact hd.trans (by norm_num)
  · let P : Sylow p G := Classical.choice inferInstance
    apply prime_pow_dvd_degree_twelve_bound p e hp htwo
    exact (P.pow_dvd_card_of_pow_dvd_card he).trans (hodd p htwo P)

/-- A finite simple group with a rational-valued irreducible character of
degree twelve and a Sylow two-subgroup of order 64 satisfies Schur's bound.
The factor `2^6` comes from the Sylow hypothesis. -/
public theorem IsIrreducibleCharacter.card_dvd_degree_twelve_bound
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Nat.card S = 64) {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hdegree : χ 1 = 12)
    (hrat : ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ)) :
    Nat.card G ∣ 2^6 * 3^8 * 5^3 * 7^2 * 11 * 13 := by
  obtain ⟨ρ, rfl, hfaithful⟩ := hχ.exists_faithful_degree_twelve hdegree
  apply card_dvd_degree_twelve_bound_of_sylow_bounds S hS
  intro p hp _ P
  exact ρ.sylow_card_dvd_pow_mul_factorial_of_rational_character hfaithful hrat P

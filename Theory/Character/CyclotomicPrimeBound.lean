module

public import Theory.FieldTheory.CyclotomicMatching
public import Theory.Character.PrimePowerTrace
public import Theory.Character.Integrality
public import Theory.Character.IrreducibleDegrees
public import Theory.Character.SimpleFaithful
public import Theory.FieldTheory.RationalDescent
public import Mathlib.GroupTheory.Sylow

/-!
# Prime divisors bounded by a fifth-cyclotomic character degree

If a character is fixed by every automorphism fixing the fifth roots of unity,
its value at an element of prime order `p > 5` is rational. More generally, a
character fixed over the `m`-th roots is rational at elements of order coprime
to `m`: CRT matches an arbitrary automorphism on the relevant roots while
fixing the `m`-th roots. The eigenvalue trace formula transfers this agreement
to the character value, and algebraicity gives rational descent.

For a faithful representation, Cauchy's theorem and Schur's prime-power trace
spacing then imply `p - 1 ≤ dimension`. Nonlinear irreducible representations
of simple groups are faithful, giving the character-degree bound. Only the
individual coprime-order values are descended; no rational model is needed.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 385–386.
-/

noncomputable section

/-- A character fixed by automorphisms fixing the `m`-th roots is rational
at every element of order coprime to `m`. -/
public theorem Representation.character_rational_of_fixed_coprime_roots
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {m : ℕ} (hm : m ≠ 0)
    (hfixed : ∀ σ : ℂ ≃+* ℂ, (∀ w : ℂ, w ^ m = 1 → σ w = w) →
      ∀ g, σ (ρ.character g) = ρ.character g)
    (g : G) (hcop : (orderOf g).Coprime m) :
    ∃ q : ℚ, ρ.character g = (q : ℂ) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  apply Complex.exists_ratCast_of_isAlgebraic_of_fixed
  · exact (IsIntegral.tower_top (A := ℚ) (character_value_isIntegral ρ g)).isAlgebraic
  · intro σ
    obtain ⟨τ, hτ, hτfix⟩ := Section1.complex_galois_aut_match_roots
      (orderOf_pos g).ne' hm hcop σ
    have hpow : (ρ g) ^ orderOf g = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    let f : Module.End ℂ V := ρ g
    have htrace : ρ.character g = ∑ μ : f.Eigenvalues,
        (μ : ℂ) * Module.finrank ℂ (f.eigenspace (μ : ℂ)) := by
      simpa [Representation.character] using
        Representation.trace_pow_eq_sum_eigenvalues (f := ρ g) (k := 1)
          (orderOf_pos g).ne' hpow
    calc
      σ (ρ.character g) = τ (ρ.character g) := by
        rw [htrace, map_sum, map_sum]
        apply Finset.sum_congr rfl
        intro μ _
        rw [map_mul, map_mul, map_natCast, map_natCast]
        rw [hτ (μ : ℂ)
          (Representation.eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property)]
      _ = ρ.character g := hfixed τ.toRingEquiv hτfix g

/-- A faithful representation whose character is fixed over the fifth roots
bounds every prime divisor greater than five by its dimension plus one. -/
public theorem Representation.prime_le_finrank_add_one_of_fixed_fifth_roots
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hfaithful : Function.Injective ρ)
    (hfixed : ∀ σ : ℂ ≃+* ℂ, (∀ w : ℂ, w ^ 5 = 1 → σ w = w) →
      ∀ g, σ (ρ.character g) = ρ.character g)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hdiv : p ∣ Nat.card G) :
    p ≤ Module.finrank ℂ V + 1 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdiv
  have hcop : (orderOf g).Coprime 5 := by
    rw [hg, hp.coprime_iff_not_dvd]
    intro hd
    have := Nat.le_of_dvd (by decide : 0 < 5) hd
    omega
  have hrat := ρ.character_rational_of_fixed_coprime_roots (by decide) hfixed g hcop
  have hpow : (ρ g) ^ (p ^ 1) = 1 := by
    rw [pow_one, ← hg, ← map_pow, pow_orderOf_eq_one, map_one]
  have hne : ρ g ≠ 1 := by
    intro he
    have hg1 := hfaithful (he.trans (map_one ρ).symm)
    simp [hg1] at hg
    omega
  obtain ⟨j, hj, _⟩ := prime_power_trace_spacing_of_rational (ρ g) hp hpow hne hrat
  have := (Nat.div_pos_iff.mp (show 0 < Module.finrank ℂ V / (p - 1) by omega)).2
  omega

/-- The cyclotomic prime bound for nonlinear irreducible characters of finite
simple groups, as used by Lyons. -/
public theorem IsIrreducibleCharacter.prime_le_degree_add_one_of_fixed_fifth_roots
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (hdegree : 1 < hχ.degree)
    (hfixed : ∀ σ : ℂ ≃+* ℂ, (∀ w : ℂ, w ^ 5 = 1 → σ w = w) →
      ∀ g, σ (χ g) = χ g)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hdiv : p ∣ Nat.card G) :
    p ≤ hχ.degree + 1 := by
  obtain ⟨n, ρ, hρ, heq⟩ := id hχ
  have hn : n = hχ.degree := by
    have hd := (congrFun heq 1).symm.trans hχ.degree_eq
    exact_mod_cast (by simpa using hd : (n : ℂ) = (hχ.degree : ℂ))
  let : Representation.IsIrreducible ρ := hρ
  have hdim : 1 < Module.finrank ℂ (Fin n → ℂ) := by simpa [hn] using hdegree
  have hfaith := ρ.injective_of_isSimpleGroup_of_one_lt_finrank hdim
  have hf : ∀ σ : ℂ ≃+* ℂ, (∀ w : ℂ, w ^ 5 = 1 → σ w = w) →
      ∀ g, σ (ρ.character g) = ρ.character g := by simpa [heq] using hfixed
  simpa [hn] using ρ.prime_le_finrank_add_one_of_fixed_fifth_roots hfaith hf hp hp5 hdiv

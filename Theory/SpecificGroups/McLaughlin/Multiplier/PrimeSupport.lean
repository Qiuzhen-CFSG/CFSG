module

public import Theory.SpecificGroups.McLaughlin.Multiplier.Basic

/-!
# Prime support of perfect central kernels over McLaughlin

The certified model order is `2^7 * 3^6 * 5^3 * 7 * 11`. Away from 2, 3
and 5 its Sylow subgroups have order at most their prime and hence are cyclic.
Central transfer therefore excludes all those primes from every finite
perfect central kernel, including primes absent from the base order.

This is the I.1.2 reduction for the McL row of Aschbacher–Smith I.1.4(2),
printed pp.407–408. Applied to the literal A.2.19 source map, it leaves only
3 and 5 for a nontrivial odd-primary center. Exclusion of 5 remains necessary
before this can supply the three-group-center input to `qt-a02-sporadic`.
-/

namespace Theory.SpecificGroups.McLaughlin.Multiplier

open Atlas.Sporadic.McLaughlin PerfectCentralCovering Subgroup

private theorem square_not_dvd_model_card {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    ¬ p ^ 2 ∣ Nat.card Model := by
  intro h
  have hd : p ∣ Nat.card Model := (dvd_pow_self p (by decide : 2 ≠ 0)).trans h
  rw [card_factorization] at hd
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11)] at hd
  rcases hd with (((h2 | h3) | h5) | h7) | h11
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3))
  · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp
      (hp.dvd_of_dvd_pow h5))
  · subst p
    rw [card_factorization] at h
    norm_num at h
  · subst p
    rw [card_factorization] at h
    norm_num at h

/-- The Sylow subgroups away from 2, 3 and 5 are cyclic. -/
public theorem sylow_isCyclic_of_ne_two_three_five {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (P : Sylow p Model) :
    IsCyclic P := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! hh
    exact square_not_dvd_model_card Fact.out hp2 hp3 hp5
      ((pow_dvd_pow p hh).trans (hn ▸ (P : Subgroup Model).card_subgroup_dvd_card))
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [hn]
  simpa only [pow_one] using pow_dvd_pow p hnle

variable {E : Type*} [Group E] [Finite E]

/-- Every other prime is excluded from every finite perfect central kernel. -/
public theorem not_dvd_kernel_of_ne_two_three_five (f : Cover E Model)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact p.Prime := ⟨hp⟩
  exact f.not_dvd_card_multiplier_of_isCyclic_sylow
    (sylow_isCyclic_of_ne_two_three_five hp2 hp3 hp5)

/-- Prime support of the actual kernel, not merely of the base-group order. -/
public theorem kernel_prime_support (f : Cover E Model) {p : ℕ}
    (hp : p.Prime) (hd : p ∣ Nat.card f.toMonoidHom.ker) :
    p = 2 ∨ p = 3 ∨ p = 5 := by
  by_contra! h
  exact not_dvd_kernel_of_ne_two_three_five f hp h.1 h.2.1 h.2.2 hd

/-- A nontrivial odd-primary kernel has prime 3 or 5. -/
public theorem odd_kernel_prime_eq_three_or_five (f : Cover E Model) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hkp : IsPGroup p f.toMonoidHom.ker)
    (hne : f.toMonoidHom.ker ≠ ⊥) : p = 3 ∨ p = 5 := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hkp.card_eq_or_dvd with h | h
  · exact (hne (Subgroup.card_eq_one.mp h)).elim
  · exact (kernel_prime_support f hp h).resolve_left hp2

/-- The literal quotient-map application in A.2.19, with the remaining
five-primary possibility retained explicitly. -/
public theorem source_center_prime_eq_three_or_five [Group.IsPerfect E]
    (e : E ⧸ center E ≃* Model) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : IsPGroup p (center E)) (hne : center E ≠ ⊥) : p = 3 ∨ p = 5 := by
  apply odd_kernel_prime_eq_three_or_five (sourceCover e) hp hp2
  · rwa [sourceCover_kernel]
  · rwa [sourceCover_kernel]

end Theory.SpecificGroups.McLaughlin.Multiplier

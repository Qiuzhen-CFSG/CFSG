module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.Basic
public import Theory.GroupTheory.PerfectCentralCoverSylowNine

/-!
# The odd part of the PSL₃(4) universal kernel

The actual projective matrix group has order `2^6 * 3^2 * 5 * 7`.
Its Sylow subgroups away from two and three are cyclic, so central Sylow
transfer excludes those primes from every perfect central kernel. The
order-nine Sylow theorem bounds the three-primary part by three.

Applied to the literal canonical universal projection, these deductions
prove that the odd part of the kernel order divides three. They leave the
exceptional two-primary calculation separate and make no use of a
multiplier table or of a construction realizing the kernel.

Source: Aschbacher–Smith I.1.2–I.1.3(6), printed p.407 (PDF p.418),
and the central-transfer proofs in `PerfectCentralCoverSylowNine`.
-/

public section

open Theory.GroupTheory PerfectCentralCovering

namespace Matrix.PSL3.ExceptionalFourCover

private theorem base_factorization (p : ℕ) :
    (Nat.card PSL3Four.PSL).factorization p =
      (if p = 2 then 6 else 0) + (if p = 3 then 2 else 0) +
      (if p = 5 then 1 else 0) + (if p = 7 then 1 else 0) := by
  rw [PSL3Four.card_PSL, show 20160 = 2^6 * 3^2 * 5 * 7 by decide]
  have h5 : Nat.Prime 5 := by decide
  have h7 : Nat.Prime 7 := by decide
  rw [Nat.factorization_mul (a := 2^6 * 3^2 * 5) (b := 7) (by decide) (by decide),
    Nat.factorization_mul (a := 2^6 * 3^2) (b := 5) (by decide) (by decide),
    Nat.factorization_mul (a := 2^6) (b := 3^2) (by decide) (by decide),
    Nat.factorization_pow, Nat.factorization_pow,
    Nat.prime_two.factorization, Nat.prime_three.factorization,
    h5.factorization, h7.factorization]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, eq_comm]
  split_ifs <;> omega

/-- Sylow subgroups away from two and three in the actual matrix group are cyclic. -/
theorem sylow_isCyclic_of_ne_two_three {p : ℕ} [Fact p.Prime]
    (h2 : p ≠ 2) (h3 : p ≠ 3) (P : Sylow p PSL3Four.PSL) : IsCyclic P := by
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [P.card_eq_multiplicity]
  have hf : (Nat.card PSL3Four.PSL).factorization p ≤ 1 := by
    rw [base_factorization]
    split_ifs <;> omega
  simpa using pow_dvd_pow p hf

/-- Only two and three can divide the canonical covering kernel order. -/
theorem kernel_prime_dvd_eq_two_or_three {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card cover.toMonoidHom.ker) : p = 2 ∨ p = 3 := by
  by_contra h
  have h2 : p ≠ 2 := fun he => h (Or.inl he)
  have h3 : p ≠ 3 := fun he => h (Or.inr he)
  let : Fact p.Prime := ⟨hp⟩
  exact (universalCover PSL3Four.PSL).not_dvd_card_multiplier_of_isCyclic_sylow
    (sylow_isCyclic_of_ne_two_three h2 h3) hd

/-- The order-nine Sylow subgroup bounds the three-primary kernel by three. -/
theorem kernel_not_nine_dvd : ¬ 9 ∣ Nat.card cover.toMonoidHom.ker := by
  let P : Sylow 3 PSL3Four.PSL := Classical.choice inferInstance
  apply (universalCover PSL3Four.PSL).not_nine_dvd_card_kernel_of_sylow_nine P
  rw [P.card_eq_multiplicity, base_factorization]
  norm_num

/-- The odd part of the actual universal covering kernel divides three. -/
theorem kernel_odd_part_dvd_three :
    ordCompl[2] (Nat.card cover.toMonoidHom.ker) ∣ 3 := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd 3 _).mpr
  intro p k hp hpk
  by_cases hk : k = 0
  · subst k
    simp
  have hdodd : p ∣ ordCompl[2] (Nat.card cover.toMonoidHom.ker) :=
    (dvd_pow_self p hk).trans hpk
  have hd : p ^ k ∣ Nat.card cover.toMonoidHom.ker :=
    hpk.trans (Nat.ordCompl_dvd _ 2)
  have hpd : p ∣ Nat.card cover.toMonoidHom.ker := (dvd_pow_self p hk).trans hd
  have hp3 : p = 3 := (kernel_prime_dvd_eq_two_or_three hp hpd).resolve_left (by
    intro hp2
    exact Nat.not_dvd_ordCompl Nat.prime_two Nat.card_pos.ne' (hp2 ▸ hdodd))
  subst p
  have hle : k ≤ 1 := by
    by_contra h
    exact kernel_not_nine_dvd ((pow_dvd_pow 3 (by omega : 2 ≤ k)).trans hd)
  simpa using pow_dvd_pow 3 hle

end Matrix.PSL3.ExceptionalFourCover

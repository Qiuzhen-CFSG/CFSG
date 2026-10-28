module

public import GorensteinWalter.PSL2DihedralSylow

/-!
# Large dihedral Sylow subgroups for adjacent-power prime fields

If p ≥ 7 and one of p − 1, p + 1 is a power of two, sixteen divides
(p − 1)(p + 1). The order formula makes eight divide |PSL₂(p)|.
Consequently its concrete dihedral Sylow model has order at least eight.
This is the prime-linear Sylow calculation in Aschbacher--Smith 2.5.8(3),
printed p.556; the precise Fermat/Mersenne domain is supplied by 2.5.2(4).
-/

public section
open scoped MatrixGroups
namespace Theory.PSL2

/-- The order of the actual prime-field projective group is divisible by eight. -/
theorem eight_dvd_card_of_adjacent_power {p k : ℕ} [Fact p.Prime]
    (hp7 : 7 ≤ p) (hpk : p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k) :
    8 ∣ Nat.card PSL(2, ZMod p) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hk : 3 ≤ k := by
    by_contra! hh
    interval_cases k <;> norm_num at hpk <;> omega
  have h8 : 8 ∣ 2 ^ k := pow_dvd_pow 2 hk
  have hsub : 2 ∣ p - 1 := by
    obtain ⟨a, ha⟩ := hpodd
    exact ⟨a, by omega⟩
  have hadd : 2 ∣ p + 1 := by
    obtain ⟨a, ha⟩ := hpodd
    exact ⟨a + 1, by omega⟩
  have h16 : 16 ∣ (p - 1) * (p + 1) := by
    rcases hpk with h | h
    · exact Nat.mul_dvd_mul (h ▸ h8) hadd
    · exact Nat.mul_dvd_mul hsub (h ▸ h8)
  have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    nlinarith [Nat.sub_add_cancel (show 1 ≤ p by omega),
      Nat.sub_add_cancel (show 1 ≤ p ^ 2 by nlinarith)]
  have hcard := GorensteinWalter.psl2_card_formula (ZMod p)
    ⟨p, 1, Fact.out, hpodd, by omega, by simp⟩
  rw [hcard, Nat.card_zmod, hsq]
  exact Nat.dvd_div_of_mul_dvd (dvd_mul_of_dvd_right h16 p)

/-- Every Sylow two-subgroup is dihedral of order at least eight. -/
theorem sylow_dihedral_of_adjacent_power {p k : ℕ} [Fact p.Prime]
    (hp7 : 7 ≤ p) (hpk : p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k)
    (P : Sylow 2 PSL(2, ZMod p)) :
    ∃ m : ℕ, 2 ≤ m ∧ Nonempty (P ≃* DihedralGroup (2 ^ m)) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨m, hm, ⟨e⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model
    (ZMod p) ⟨p, 1, Fact.out, hpodd, by omega, by simp⟩ P
  have h8P := P.pow_dvd_card_of_pow_dvd_card (n := 3)
    (eight_dvd_card_of_adjacent_power hp7 hpk)
  refine ⟨m, ?_, ⟨e⟩⟩
  by_contra! hh
  have hm1 : m = 1 := by omega
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hm1] at h8P
  norm_num at h8P

end Theory.PSL2

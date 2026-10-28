module

public import GorensteinWalter.PSL2DihedralSylow
public import GorensteinWalter.DihedralUniqueCentralInvolution

/-!
# Sylow centers of prime-field PSL₂ with an adjacent power of two

For a prime p ≥ 7 with p − 1 or p + 1 a power of two, eight divides
|PSL₂(p)|. The proved split and nonsplit torus constructions identify every
Sylow two-subgroup with a dihedral group. Its order is divisible by eight,
so its center has at most two elements: every central element squares to
one, and the nonidentity central involution is unique.

The projective group is the actual matrix quotient. The proof reuses the
intrinsic torus and order results in GorensteinWalter.PSL2DihedralSylow,
which derive from Huppert II.8.3–4, without a classification hypothesis.
This supplies the odd-prime Sylow-center calculation in Aschbacher–Smith
15.4.20, printed p.1164, with the inner actions from 1.1.5(3)(e).
-/

open scoped MatrixGroups
open Subgroup
namespace Theory.PSL2.SylowFixedQuotients

private theorem dihedral_center_card_le_two {m : ℕ} (hm : 2 ≤ m) :
    Nat.card (center (DihedralGroup (2 ^ m))) ≤ 2 := by
  classical
  have hsq (x : center (DihedralGroup (2 ^ m))) : (x : DihedralGroup (2 ^ m)) ^ 2 = 1 := by
    obtain ⟨i, hi⟩ | ⟨i, hi⟩ := GorensteinWalter.dihedralGroup_cases x.val
    · have hc := mem_center_iff.mp x.property (DihedralGroup.sr 0)
      rw [hi] at hc
      have hneg : i = -i := by
        simpa only [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, zero_add,
          zero_sub, DihedralGroup.sr.injEq] using hc
      rw [hi, pow_two, DihedralGroup.r_mul_r]
      rw [eq_neg_iff_add_eq_zero.mp hneg]
      rfl
    · rw [hi, pow_two, DihedralGroup.sr_mul_self]
  let f : center (DihedralGroup (2 ^ m)) → Bool := fun x => decide (x = 1)
  have hf : Function.Injective f := by
    intro x y hxy
    have he : (x = 1 ↔ y = 1) := by simpa only [f, decide_eq_decide] using hxy
    by_cases hx : x = 1
    · exact hx.trans (he.mp hx).symm
    · have hy : y ≠ 1 := fun hy => hx (he.mpr hy)
      apply Subtype.ext
      exact (GorensteinWalter.unique_central_involution_of_dihedral_two_pow hm
        x.val x.property (hsq x) (fun h => hx (Subtype.ext h))).trans
        (GorensteinWalter.unique_central_involution_of_dihedral_two_pow hm
          y.val y.property (hsq y) (fun h => hy (Subtype.ext h))).symm
  simpa using Nat.card_le_card_of_injective f hf

private theorem eight_dvd_card {p k : ℕ} [Fact p.Prime]
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

/-- The Sylow-center bound for the actual PSL₂ prime-field model.
The adjacent-power hypothesis is the arithmetic input used for Fermat
and Mersenne primes; p ≥ 7 excludes the Sylow four-group in PSL₂(5). -/
public theorem sylow_center_card_le_two_of_adjacent_power {p k : ℕ} [Fact p.Prime]
    (hp7 : 7 ≤ p) (hpk : p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k)
    (P : Sylow 2 PSL(2, ZMod p)) : Nat.card (center P) ≤ 2 := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨m, hm, ⟨e⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model
    (ZMod p) ⟨p, 1, Fact.out, hpodd, by omega, by simp⟩ P
  have h8 : 8 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n := 3) (eight_dvd_card hp7 hpk)
  have hm2 : 2 ≤ m := by
    by_contra! hh
    have hm1 : m = 1 := by omega
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hm1] at h8
    norm_num at h8
  rw [Nat.card_congr (centerCongr e).toEquiv]
  exact dihedral_center_card_le_two hm2

end Theory.PSL2.SylowFixedQuotients

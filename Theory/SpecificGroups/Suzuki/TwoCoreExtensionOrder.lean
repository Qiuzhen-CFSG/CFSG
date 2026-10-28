module

public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import Theory.PGroupCore

/-!
# Three-free orders for Suzuki two-core extensions

For q = 2^(2m+1), q is two modulo three, so none of q², q²+1, q-1
is divisible by three. The checked order formula for the concrete Suzuki
matrix group therefore excludes three. The same holds for any finite group
whose quotient by its actual two-core is isomorphic to that Suzuki group.

This is the arithmetic input for the Suzuki-side local factor in
Aschbacher–Smith 2.3.9(7), printed p.526, using the local quotient described
in F.1.12(I)(5), printed p.263. It asserts no Ree subgroup construction.
The Suzuki order formula is Huppert–Blackburn III, XI.3.3.
-/

open Subgroup
namespace BenderSuzuki.MatrixGroups

/-- The actual Suzuki group over a field of odd binary degree has order prime to three. -/
public theorem suzukiMatrixGroup_three_free (m : ℕ) (hm : 0 < m) :
    ¬ 3 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m hm]
  have hfour : 4 ^ m % 3 = 1 := by
    change Nat.ModEq 3 (4 ^ m) 1
    simpa only [one_pow] using
      (show Nat.ModEq 3 4 1 by norm_num [Nat.ModEq]).pow m
  have hq : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul]
    norm_num only [Nat.reducePow] at *
    rw [Nat.mul_mod, hfour]
  have hsq : (2 ^ (2 * m + 1)) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  have hsub : (2 ^ (2 * m + 1) - 1) % 3 = 1 := by
    generalize 2 ^ (2 * m + 1) = q at hq ⊢
    omega
  intro hd
  rcases Nat.prime_three.dvd_mul.mp hd with hd | hd
  · rcases Nat.prime_three.dvd_mul.mp hd with hd | hd
    · have hz := Nat.dvd_iff_mod_eq_zero.mp hd
      rw [Nat.add_mod, hsq] at hz
      norm_num at hz
    · have hz := Nat.dvd_iff_mod_eq_zero.mp hd
      omega
  · have hz := Nat.dvd_iff_mod_eq_zero.mp hd
    omega

/-- A two-core extension of the actual Suzuki group also has order prime to three. -/
public theorem three_free_of_suzuki_core_quotient {P : Type*} [Group P] [Finite P]
    (m : ℕ) (hm : 0 < m)
    (e : (P ⧸ pCore 2 P) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    ¬ 3 ∣ Nat.card P := by
  have hq : ¬ 3 ∣ Nat.card (P ⧸ pCore 2 P) := by
    rw [Nat.card_congr e.toEquiv]
    exact suzukiMatrixGroup_three_free m hm
  intro hd
  rw [← (pCore 2 P).card_mul_index] at hd
  rcases Nat.prime_three.dvd_mul.mp hd with hc | hi
  · obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := P)).exists_card_eq
    rw [hn] at hc
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hc)
  · exact hq ((pCore 2 P).index_eq_card ▸ hi)

end BenderSuzuki.MatrixGroups

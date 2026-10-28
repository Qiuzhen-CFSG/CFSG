module
public import Theory.SpecificGroups.Suzuki.SubgroupParameters

/-!
# Five divides the Suzuki group order

For q = 2^(2m+1), the factor q²+1 is divisible by five. Apply the
checked Suzuki order formula (Huppert–Blackburn III, XI.3.3). This supplies
the Suzuki branch of prime-to-15 solvability for the known-simple class.
-/

public section
namespace BenderSuzuki.MatrixGroups

theorem suzukiMatrixGroup_five_dvd (m : ℕ) (hm : 0 < m) :
    5 ∣ Nat.card (SuzukiMatrixGroup m) := by
  rw [suzukiMatrixGroup_card m hm]
  have hpow : Nat.ModEq 5 (16 ^ m) 1 := by
    simpa using (show Nat.ModEq 5 16 1 by decide).pow m
  have hq : (2 ^ (2 * m + 1)) ^ 2 % 5 = 4 := by
    have he : (2 ^ (2 * m + 1)) ^ 2 = 16 ^ m * 4 := by
      rw [← pow_mul]
      have hn : (2 * m + 1) * 2 = 4 * m + 2 := by omega
      rw [hn, pow_add, pow_mul]
      norm_num
    rw [he, Nat.mul_mod, hpow]
  have hd : 5 ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    rw [Nat.add_mod, hq]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
end BenderSuzuki.MatrixGroups

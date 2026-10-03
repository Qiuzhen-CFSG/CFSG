module

public import BenderSuzuki.MatrixGroups.SuzukiSubfieldEmbedding
public import BenderSuzuki.Converse.Sz
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import BenderSuzuki.MatrixGroups.SuzukiModel
public import Theory.GroupTheory.MinimalSimple

/-!
# Prime exponents in the Suzuki family

A composite odd exponent `2*n+1`, with `n >= 1`, has a proper divisor
`2*d+1` with `d >= 1`. The compatible subfield embedding realizes the
smaller Suzuki group inside the larger one. The smaller group is nonsolvable,
so minimal simplicity would force this embedding to be surjective, contrary
to the strictly increasing Suzuki order formula. The final interface uses
the shared model and transports along an actual group isomorphism.

Source: Thompson's Suzuki family and the standard Suzuki subfield argument;
Huppert--Blackburn XI.3.3 and XI.3.6 supply order and nonsolvability.
-/

namespace Stellmacher.Recognition

open BenderSuzuki.MatrixGroups BenderSuzuki.External

private theorem suzuki_card (n : ℕ) (hn : 0 < n) :
    Nat.card (SuzukiMatrixGroup n) =
      ((2 ^ (2 * n + 1)) ^ 2 + 1) * (2 ^ (2 * n + 1)) ^ 2 *
        (2 ^ (2 * n + 1) - 1) :=
  (BenderSuzuki.Converse.sz_data n hn).2.2.2.2.1

private theorem suzuki_card_lt {d n : ℕ} (hd : 0 < d) (hdn : d < n) :
    Nat.card (SuzukiMatrixGroup d) < Nat.card (SuzukiMatrixGroup n) := by
  rw [suzuki_card d hd, suzuki_card n (by omega)]
  have hq : (2 : ℕ) ^ (2 * d + 1) < 2 ^ (2 * n + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hqpos : 0 < (2 : ℕ) ^ (2 * d + 1) := by positivity
  have hsq : ((2 : ℕ) ^ (2 * d + 1)) ^ 2 ≤ (2 ^ (2 * n + 1)) ^ 2 :=
    Nat.pow_le_pow_left hq.le 2
  have hsub : (2 : ℕ) ^ (2 * d + 1) - 1 < 2 ^ (2 * n + 1) - 1 := by omega
  exact (Nat.mul_lt_mul_of_pos_left hsub (by positivity)).trans_le
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) hsq))

/-- Minimal simplicity of a concrete Suzuki matrix group forces prime odd degree. -/
public theorem minimalSimple_suzuki_matrix_exponent_prime {n : ℕ} (hn : 1 ≤ n)
    (hG : IsMinimalSimple (SuzukiMatrixGroup n)) : (2 * n + 1).Prime := by
  by_contra hnot
  obtain ⟨r, hrdiv, hr, hrlt⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hnot
  have hrodd : Odd r := (show Odd (2 * n + 1) from ⟨n, rfl⟩).of_dvd_nat hrdiv
  obtain ⟨d, rfl⟩ := hrodd
  have hd : 0 < d := by omega
  have hdn : d < n := by omega
  obtain ⟨f, hf⟩ := exists_suzuki_subfield_embedding hrdiv
  have hsurj := hG.surjective_of_injective (suzukiMatrixGroup_not_isSolvable d hd) f hf
  have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hf, hsurj⟩)
  exact (suzuki_card_lt hd hdn).ne hcard

/-- Minimal simplicity forces prime odd degree in the shared Suzuki model. -/
public theorem minimalSimple_suzuki_exponent_prime {n : ℕ} (hn : 1 ≤ n)
    (hG : IsMinimalSimple (SzModel n)) : (2 * n + 1).Prime := by
  rw [szModel_eq_suzukiMatrixGroup] at hG
  exact minimalSimple_suzuki_matrix_exponent_prime hn hG

/-- A minimal-simple group identified with a Suzuki model has prime odd degree. -/
public theorem minimalSimple_suzuki_branch_prime
    {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 1 ≤ n)
    (hG : IsMinimalSimple G) (e : G ≃* SzModel n) : (2 * n + 1).Prime :=
  minimalSimple_suzuki_exponent_prime hn (hG.of_mulEquiv e)

end Stellmacher.Recognition

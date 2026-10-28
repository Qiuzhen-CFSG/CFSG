module

public import BenderSuzuki.MatrixGroups.BinarySubfieldEmbedding
public import Stellmacher.Recognition.ConversePSL2Binary
public import Theory.Comparator.Defs

/-!
# Prime exponents in the binary PSL2 family

A composite exponent n >= 2 has a proper divisor d with 2 <= d < n.
The binary subfield embedding supplies an injective homomorphism from
PSL2(2^d) to PSL2(2^n). The source group is nonsolvable by perfection, so
minimal simplicity forces this map to be surjective. The exact projective
order formula is strictly increasing in the field degree, contradicting
surjectivity.

Together with the proved binary converse this gives the iff between minimal
simplicity and prime exponent for the binary family. The embedding is built
from the actual finite-field algebra homomorphism and the characteristic-two
SL2/PSL2 quotient equivalences.

Source: Thompson's binary family and the standard finite-field subfield
argument; order and perfection interfaces are exported by the existing
Bender--Suzuki and Gorenstein--Walter developments.
-/

namespace Stellmacher.Recognition

open BenderSuzuki.MatrixGroups BenderSuzuki.External GorensteinWalter

private theorem binary_card (f : ℕ) (hf : f ≠ 0) :
    Nat.card (PSL2MatrixGroup (GaloisField 2 f)) =
      2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have hcard := huppert614_card_psl_mul_center (K := GaloisField 2 f)
  have hcenter := huppert614_card_center_of_neg_one_eq_one (K := GaloisField 2 f)
    (CharTwo.neg_eq 1)
  rw [hcenter, mul_one, GaloisField.card 2 f hf] at hcard
  exact hcard

private theorem binary_card_lt_of_degree_lt
    {d n : ℕ} (hd : 2 ≤ d) (hdn : d < n) :
    Nat.card (PSL2MatrixGroup (GaloisField 2 d)) <
      Nat.card (PSL2MatrixGroup (GaloisField 2 n)) := by
  rw [binary_card d (by omega), binary_card n (by omega)]
  have hq : 2 ^ d < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hdn
  have hdpos : 0 < (2 : ℕ) ^ d := by positivity
  have hd4 : 4 ≤ (2 : ℕ) ^ d := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have hsq : ((2 : ℕ) ^ d) ^ 2 < ((2 : ℕ) ^ n) ^ 2 :=
    Nat.pow_lt_pow_left hq (by norm_num)
  have hsub : ((2 : ℕ) ^ d) ^ 2 - 1 < ((2 : ℕ) ^ n) ^ 2 - 1 := by
    have hsqpos : 0 < ((2 : ℕ) ^ d) ^ 2 := by positivity
    omega
  exact (Nat.mul_lt_mul_of_pos_left hsub hdpos).trans_le
    (Nat.mul_le_mul_right _ hq.le)

/-- Minimal simplicity forces a prime exponent in the binary PSL2 family. -/
public theorem minimalSimple_binary_exponent_prime
    {n : ℕ} (hn : 2 ≤ n) (hG : IsMinimalSimple (PSL2MatrixGroup (GaloisField 2 n))) :
    n.Prime := by
  by_contra hnot
  obtain ⟨d, hdiv, hd, hdn⟩ := Nat.exists_dvd_of_not_prime2 hn hnot
  obtain ⟨f, hf⟩ := exists_binary_psl2_embedding (by omega) (by omega) hdiv
  have hdcard : 4 ≤ Nat.card (GaloisField 2 d) := by
    rw [GaloisField.card 2 d (by omega)]
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  let : Group.IsPerfect (PSL2MatrixGroup (GaloisField 2 d)) :=
    psl2_isPerfect_of_card_gt_three _ (by omega)
  have hns : ¬ Group.IsSolvable (PSL2MatrixGroup (GaloisField 2 d)) :=
    Group.IsPerfect.not_isSolvable _
  have hsurj := hG.surjective_of_injective hns f hf
  have hcardEq := Nat.card_congr (Equiv.ofBijective f ⟨hf, hsurj⟩)
  exact (binary_card_lt_of_degree_lt hd hdn).ne hcardEq

/-- Binary PSL2 is minimal simple exactly at prime exponents n >= 2. -/
public theorem isMinimalSimple_psl2_binary_iff
    {n : ℕ} (hn : 2 ≤ n) :
    IsMinimalSimple (PSL2MatrixGroup (GaloisField 2 n)) ↔ n.Prime :=
  ⟨minimalSimple_binary_exponent_prime hn, isMinimalSimple_psl2_binary⟩

/-- A minimal-simple group identified with a binary PSL2 model has prime
field exponent. -/
public theorem minimalSimple_binary_branch_prime
    {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 2 ≤ n)
    (hG : IsMinimalSimple G) (e : G ≃* PSL2Model n) : n.Prime := by
  exact minimalSimple_binary_exponent_prime hn (hG.of_mulEquiv e)

end Stellmacher.Recognition

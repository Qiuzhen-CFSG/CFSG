module
public import ABG.ChapterII.Section2.UnitaryLevelCard

/-!
# Cardinality of the actual two-dimensional unitary group

For odd prime p and nonzero n, the original GU2 over GF(p^(2n)) has order
q(q^2-1)(q+1), where q=p^n. In particular, the formula includes q=3 and q=9.
This supplies the ambient order for comparing a fixed-unitary subgroup
under an odd-degree coefficient-field extension.

The determinant kernel is the actual level-zero subgroup, whose order was
proved using the actual SU2--SL2 equivalence. The determinant range is the
full norm-one roots subgroup, of order q+1 by finite-field roots counting.
Multiplying the kernel order by its index gives the result, without an
assumed unitary cardinality or abstract recognition theorem.

Source: ABG II.2 Lemma 1 proof, article page 17; the fixed-unitary Sylow
construction in II.3 Proposition 3 uses this exact original Hermitian model.
-/

namespace ABG
open Matrix.GeneralLinearGroup

public theorem GU2_card
    (p n : ℕ) [Fact p.Prime] (hp : Odd p) (hn : n ≠ 0) :
    Nat.card (GU2 p n hn) = p ^ n * ((p ^ n) ^ 2 - 1) * (p ^ n + 1) := by
  let F := GaloisField p (2 * n)
  let f : GU2 p n hn →* Fˣ :=
    (det : GL (Fin 2) F →* Fˣ).comp (unitaryForm 2 p n hn).unitarySubgroup.subtype
  have hk : SU2Level p n hn 0 = f.ker := by
    ext A
    change (det A.val ^ (2 ^ 0) = 1) ↔ det A.val = 1
    simp only [pow_zero, pow_one]
  have hcard : Nat.card F = (p ^ n) ^ 2 := by
    rw [GaloisField.card p (2 * n) (Nat.mul_ne_zero (by decide) hn),
      ← pow_mul, Nat.mul_comm n 2]
  have hdivq : p ^ n + 1 ∣ Nat.card F - 1 := by
    rw [hcard]
    exact ⟨p ^ n - 1, by simpa only [one_pow] using Nat.sq_sub_sq (p ^ n) 1⟩
  have hidx : f.ker.index = p ^ n + 1 := by
    rw [Subgroup.index_ker, GU2_det_range p n hn]
    exact FiniteField.card_rootsOfUnity_of_dvd F (p ^ n + 1) hdivq
  have hmul := f.ker.card_mul_index
  rw [hidx, ← hk, SU2Level_card p n hp hn 0 (by simp)] at hmul
  simpa only [pow_zero, one_mul] using hmul.symm

end ABG


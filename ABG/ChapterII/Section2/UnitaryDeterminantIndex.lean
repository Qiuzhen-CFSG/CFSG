module
public import ABG.ChapterII.Section2.UnitaryDeterminantImage
public import ABG.ChapterII.Section2.UnitaryDeterminantModels
public import Theory.FieldTheory.RootsOfUnityCard
public import Mathlib.GroupTheory.Index

/-!
# Exact indices in the unitary determinant filtration

For a prime p and nonzero n, the actual unitary determinant level a has
relative index 2^(b-a) in level b whenever a≤b and 2^b divides p^n+1.
In particular level zero has index 2^m in level m, and consecutive valid
levels have index two. No oddness assumption is needed.

The original GU2 determinant has level zero as its kernel and the full
norm-one roots of unity as its image. Mapping a determinant level therefore
gives precisely its 2^m-th roots of unity. Their order is 2^m: the bound
2^m divides p^n+1, which itself divides the quadratic field's multiplicative
order. Relative-index multiplicativity then gives the general formula.

Source: ABG II.2, the definitions preceding Lemma 1, article page 17. These
indices are used for the actual unitary index-two model comparison in II.3
Proposition 3. All subgroups use the original Hermitian GU2 model; no
abstract recognition or ambient unitary cardinality formula is assumed.
-/

namespace ABG
open Matrix.GeneralLinearGroup

public theorem SU2Level_zero_relIndex
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (m : ℕ)
    (hd : 2 ^ m ∣ p ^ n + 1) :
    (SU2Level p n hn 0).relIndex (SU2Level p n hn m) = 2 ^ m := by
  let F := GaloisField p (2 * n)
  let f : GU2 p n hn →* Fˣ :=
    (det : GL (Fin 2) F →* Fˣ).comp (unitaryForm 2 p n hn).unitarySubgroup.subtype
  have hk : SU2Level p n hn 0 = f.ker := by
    ext A
    change (det A.val ^ (2 ^ 0) = 1) ↔ det A.val = 1
    simp only [pow_zero, pow_one]
  rw [hk, Subgroup.relIndex_ker]
  change Nat.card (((rootsOfUnity (2 ^ m) F).comap f).map f) = 2 ^ m
  rw [Subgroup.map_comap_eq, GU2_det_range p n hn,
    inf_eq_right.mpr (rootsOfUnity_le_of_dvd hd)]
  have hcard : Nat.card F = (p ^ n) ^ 2 := by
    rw [GaloisField.card p (2 * n) (Nat.mul_ne_zero (by decide) hn),
      ← pow_mul, Nat.mul_comm n 2]
  have hdivq : p ^ n + 1 ∣ Nat.card F - 1 := by
    rw [hcard]
    exact ⟨p ^ n - 1, by simpa only [one_pow] using Nat.sq_sub_sq (p ^ n) 1⟩
  exact FiniteField.card_rootsOfUnity_of_dvd F (2 ^ m) (hd.trans hdivq)

public theorem SU2Level_relIndex
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) {a b : ℕ} (hab : a ≤ b)
    (hd : 2 ^ b ∣ p ^ n + 1) :
    (SU2Level p n hn a).relIndex (SU2Level p n hn b) = 2 ^ (b - a) := by
  have hda : 2 ^ a ∣ p ^ n + 1 := (pow_dvd_pow 2 hab).trans hd
  have hi := Subgroup.relIndex_mul_relIndex
    (SU2Level p n hn 0) (SU2Level p n hn a) (SU2Level p n hn b)
    (SU2Level_mono p n hn (Nat.zero_le a)) (SU2Level_mono p n hn hab)
  rw [SU2Level_zero_relIndex p n hn a hda, SU2Level_zero_relIndex p n hn b hd] at hi
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < 2) a)
  rw [hi, ← pow_add, Nat.add_sub_of_le hab]

public theorem SU2Level_successor_relIndex
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (m : ℕ)
    (hd : 2 ^ (m + 1) ∣ p ^ n + 1) :
    (SU2Level p n hn m).relIndex (SU2Level p n hn (m + 1)) = 2 := by
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_left, pow_one] using
    SU2Level_relIndex p n hn (Nat.le_succ m) hd

end ABG


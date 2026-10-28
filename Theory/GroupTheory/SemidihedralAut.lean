module

public import Theory.GroupTheory.SemidihedralCenter
public import Theory.GroupTheory.CharacteristicIndexTwoAut
public import Theory.GroupTheory.CyclicTwoAut

/-!
# Automorphisms of semidihedral presentations

In the semidihedral presentation of order `2^n`, `n ≥ 4`, every element outside
the rotation subgroup has fourth power one. The rotation generator has order
at least eight, so its cyclic subgroup is characteristic. Restriction to this
index-two cyclic subgroup then proves that the automorphism group is a two-group.

Source: the elementary semidihedral calculation accompanying GLS2, Chapter C,
Sections 10.1–10.11. The parameter here is the logarithm of the group order.
-/

namespace Semidihedral
open Subgroup
variable {G : Type*} [Group G]

private theorem outside_pow_four {n : ℕ} (hn : 4 ≤ n) (a b : G)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1)) (i : ℕ) :
    (a ^ i * b) ^ 4 = 1 := by
  have hp : 0 < 2 ^ (n - 2) := by positivity
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  have hsq : (a ^ i * b) ^ 2 = a ^ (2 ^ (n - 2) * i) := by
    calc
      _ = a ^ i * (b * a ^ i) * b := by simp only [pow_two]; group
      _ = a ^ i * (a ^ ((2 ^ (n - 2) - 1) * i) * b) * b := by rw [move_pow a b _ hconj i]
      _ = a ^ (i + (2 ^ (n - 2) - 1) * i) := by
        rw [mul_assoc, mul_assoc, ← pow_two b, hb2, mul_one, ← pow_add]
      _ = _ := by
        congr 1
        have he : 1 + (2 ^ (n - 2) - 1) = 2 ^ (n - 2) := by omega
        simpa only [add_mul, one_mul] using congrArg (· * i) he
  calc
    _ = ((a ^ i * b) ^ 2) ^ 2 := by rw [← pow_mul]
    _ = a ^ ((2 ^ (n - 2) * i) * 2) := by rw [hsq, ← pow_mul]
    _ = (a ^ (2 ^ (n - 1))) ^ i := by
      rw [← pow_mul, show n - 1 = (n - 2) + 1 by omega, pow_succ]
      congr 1; ring
    _ = 1 := by rw [← ha, pow_orderOf_eq_one, one_pow]

/-- The rotation subgroup in a semidihedral presentation is characteristic. -/
public theorem rotations_characteristic {n : ℕ} (hn : 4 ≤ n) (a b : G)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : closure ({a, b} : Set G) = ⊤) : (zpowers a).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro f
  apply zpowers_le.mpr
  change f a ∈ zpowers a
  obtain ⟨i, -, h | h⟩ := normal_form a b _ _ (by positivity) ha
    (hb ▸ pow_orderOf_eq_one b) hconj hgen (f a)
  · rw [h]; exact pow_mem (mem_zpowers a) i
  · have hd := orderOf_dvd_of_pow_eq_one (outside_pow_four hn a b ha hb hconj i)
    rw [← h, f.orderOf_eq, ha] at hd
    have hl := Nat.le_of_dvd (by decide : 0 < 4) hd
    have hg : 8 ≤ 2 ^ (n - 1) := by
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ n - 1)
    omega

/-- The automorphism group of a semidihedral presentation is a two-group. -/
public theorem isPGroup_mulAut [Finite G] {n : ℕ} (hn : 4 ≤ n)
    (hcard : Nat.card G = 2 ^ n) (a b : G)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : closure ({a, b} : Set G) = ⊤) : IsPGroup 2 (MulAut G) := by
  let A := zpowers a
  let : A.Characteristic := rotations_characteristic hn a b ha hb hconj hgen
  have hG : IsPGroup 2 G := IsPGroup.of_card hcard
  have hi : A.index = 2 := by
    have h := A.index_mul_card
    have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
      omega
    rw [show Nat.card A = 2 ^ (n - 1) by rw [Nat.card_zpowers, ha], hcard, hp] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ (n - 1)) h
  exact A.isPGroup_mulAut_of_characteristic_index_two hi
    (hG.to_subgroup A) (hG.to_subgroup A).mulAut_of_isCyclic_two

end Semidihedral

module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.PGroup

/-!
# Involution centralizers in alternating groups of degree at most six

An involution has only two-cycles. Its sign is even, and at most three
two-cycles fit in degree at most six, so its cycle type is exactly (2,2).
The symmetric-group centralizer has order 8·(n−4)!, a power of two.
Its subgroup centralizing the involution inside Aₙ is therefore a two-group.

These elementary permutation calculations supply the A₅ and A₆ cases of
condition E in Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(3), printed p.4 (repeated on p.482).
-/

namespace alternatingGroup

open Subgroup Equiv.Perm

/-- Every involution in Aₙ, n ≤ 6, is a double transposition. -/
public theorem involution_cycleType_of_degree_le_six {n : ℕ} (hn : n ≤ 6)
    (x : alternatingGroup (Fin n)) (hx : orderOf x = 2) :
    (x : Equiv.Perm (Fin n)).cycleType = {2, 2} := by
  have ho : orderOf (x : Equiv.Perm (Fin n)) = 2 := (Subgroup.orderOf_coe x).trans hx
  obtain ⟨k, hk⟩ := cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hbound := (x : Equiv.Perm (Fin n)).sum_cycleType_le
  rw [hk] at hbound
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hbound
  have hsign := mem_alternatingGroup.mp x.property
  rw [sign_of_cycleType', hk] at hsign
  have hkbound : k ≤ 2 := by omega
  have hk1 : k = 1 := by
    interval_cases k
    · norm_num at hsign
    · rfl
    · norm_num at hsign
  simpa [hk1] using hk

/-- The centralizer in Aₙ of an involution is a two-group when n ≤ 6. -/
public theorem isPGroup_centralizer_involution_of_degree_le_six
    {n : ℕ} (hn : n ≤ 6) (x : alternatingGroup (Fin n)) (hx : orderOf x = 2) :
    IsPGroup 2 (centralizer ({x} : Set (alternatingGroup (Fin n)))) := by
  have hct := involution_cycleType_of_degree_le_six hn x hx
  have hc : IsPGroup 2
      (centralizer ({(x : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n)))) := by
    apply IsPGroup.of_card_dvd_pow (n := 4)
    rw [nat_card_centralizer, hct]
    norm_num
    have hsub : n - 4 ≤ 2 := by omega
    interval_cases h : n - 4 <;> norm_num [h]
  have heq : centralizer ({x} : Set (alternatingGroup (Fin n))) =
      (centralizer ({(x : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n)))).comap
        (alternatingGroup (Fin n)).subtype := by
    ext y
    simp only [mem_centralizer_singleton_iff, mem_comap, Subtype.ext_iff]
    rfl
  rw [heq]
  exact hc.comap_of_injective _ Subtype.val_injective

end alternatingGroup

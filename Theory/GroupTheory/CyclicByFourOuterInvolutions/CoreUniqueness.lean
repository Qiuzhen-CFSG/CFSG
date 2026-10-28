module

public import Theory.GroupTheory.CyclicByFourOuterInvolutions

/-!
# Uniqueness of the large inner cyclic subgroup

The cyclic-by-four normal forms have four distinct cosets: the inner
reflection is not a rotation, and the outer generator lies outside the
inner subgroup. Thus the rotation subgroup has relative index exactly four.
When the reflection is square-one, every element of its inner coset has
fourth power one. A cyclic inner subgroup of relative index at most four
has a generator of order at least eight, so it lies in the rotations and
has their full order.

This identifies an arbitrary supplied core without replacing it by a newly
chosen subgroup. The marked unitary-plane application supplies the
square-one reflection from its actual coordinate-swap matrix.

Source: the semidihedral Sylow calculation in Alperin--Brauer--Gorenstein,
II.2 Lemma 1, article p.17; Aschbacher--Smith A.3.21(b), p.55, and the
odd unitary branch of E.1.14(7), p.214.
-/

public section

open Subgroup
namespace Theory.GroupTheory.CyclicByFourCoordinates
variable {G : Type*} [Group G] {L T : Subgroup G} {z : G}

/-- The semidihedral reflection does not belong to the rotations. -/
theorem reflection_not_mem_rotations (q : CyclicByFourCoordinates L T z) :
    q.b ∉ zpowers q.a := by
  rintro ⟨i, hi⟩
  have hcomm : Commute q.b q.a := by
    rw [← hi]
    exact (Commute.refl q.a).zpow_left i
  have he : q.a ^ (2 ^ (q.n + 2) - 1) = q.a ^ 1 := by
    rw [pow_one, ← q.b_action, hcomm.eq, mul_inv_cancel_right]
  have hm : 4 ≤ 2 ^ (q.n + 2) := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ q.n + 2)
  have ho : orderOf q.a = 2 ^ (q.n + 2) * 2 := by rw [q.a_order]; ring
  have hh := pow_injOn_Iio_orderOf (x := q.a)
    (show 2 ^ (q.n + 2) - 1 < orderOf q.a by rw [ho]; omega)
    (show 1 < orderOf q.a by rw [ho]; omega) he
  omega

/-- The four normal forms are four distinct cosets of the rotations. -/
theorem rotations_relIndex [Finite G] (q : CyclicByFourCoordinates L T z) :
    (zpowers q.a).relIndex T = 4 := by
  let C := zpowers q.a
  let H := L ⊓ T
  have hCH : C ≤ H := zpowers_le.mpr ⟨q.a_inner, q.a_mem⟩
  have hHT : H ≤ T := inf_le_right
  have h1 : C.relIndex H ≠ 1 := by
    intro h
    exact q.reflection_not_mem_rotations (relIndex_eq_one.mp h ⟨q.b_inner, q.b_mem⟩)
  have h2 : H.relIndex T ≠ 1 := by
    intro h
    exact q.c_outer (relIndex_eq_one.mp h q.c_mem).1
  have h1p : C.relIndex H ≠ 0 := FiniteIndex.index_ne_zero (H := C.subgroupOf H)
  have h2p : H.relIndex T ≠ 0 := FiniteIndex.index_ne_zero (H := H.subgroupOf T)
  have h1l : 2 ≤ C.relIndex H := by omega
  have h2l : 2 ≤ H.relIndex T := by omega
  have ht := relIndex_mul_relIndex C H T hCH hHT
  have hu := q.core_relIndex
  change C.relIndex T ≤ 4 at hu
  nlinarith

/-- Every element of the inner reflection coset has order dividing four. -/
theorem reflection_coset_fourth_power (q : CyclicByFourCoordinates L T z)
    (hb : q.b ^ 2 = 1) (i : ℤ) : (q.a ^ i * q.b) ^ 4 = 1 := by
  have haction : q.b * q.a ^ i * q.b⁻¹ = (q.a ^ i) ^ (2 ^ (q.n + 2) - 1) := by
    calc
      _ = (q.b * q.a * q.b⁻¹) ^ i := map_zpow (MulAut.conj q.b) q.a i
      _ = (q.a ^ (2 ^ (q.n + 2) - 1)) ^ i := by rw [q.b_action]
      _ = _ := by
        rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, Int.mul_comm]
  have hbi : q.b⁻¹ = q.b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hb)
  have hp : 1 ≤ 2 ^ (q.n + 2) := Nat.one_le_two_pow
  have hs : (q.a ^ i * q.b) ^ 2 = (q.a ^ i) ^ (2 ^ (q.n + 2)) := by
    calc
      _ = q.a ^ i * (q.b * q.a ^ i * q.b⁻¹) := by rw [hbi, pow_two]; group
      _ = q.a ^ i * (q.a ^ i) ^ (2 ^ (q.n + 2) - 1) := by rw [haction]
      _ = _ := by rw [← pow_succ', Nat.sub_add_cancel hp]
  calc
    _ = ((q.a ^ i * q.b) ^ 2) ^ 2 := by rw [← pow_mul]
    _ = (q.a ^ i) ^ (2 ^ (q.n + 2) * 2) := by rw [hs, ← pow_mul]
    _ = (q.a ^ i) ^ (orderOf q.a) := by congr 1; rw [q.a_order]; ring
    _ = 1 := by rw [← zpow_natCast, ← zpow_mul, Int.mul_comm, zpow_mul,
      zpow_natCast, pow_orderOf_eq_one, one_zpow]

/-- Every cyclic inner subgroup of relative index at most four is the
canonical rotation subgroup. -/
theorem cyclic_inner_eq_rotations [Finite G] (q : CyclicByFourCoordinates L T z)
    (hb : q.b ^ 2 = 1) (D : Subgroup G) [IsCyclic D]
    (hDL : D ≤ L) (hDT : D ≤ T) (hidx : D.relIndex T ≤ 4) :
    D = zpowers q.a := by
  have hCT : zpowers q.a ≤ T := zpowers_le.mpr q.a_mem
  have hDC := relIndex_mul_relIndex (⊥ : Subgroup G) D T bot_le hDT
  have hCC := relIndex_mul_relIndex (⊥ : Subgroup G) (zpowers q.a) T bot_le hCT
  simp only [relIndex_bot_left, q.rotations_relIndex] at hDC hCC
  have hsize : Nat.card (zpowers q.a) ≤ Nat.card D := by nlinarith
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := D)
  have hxcard : orderOf (x : G) = Nat.card D := by
    rw [orderOf_coe]
    exact hx
  have hDx : zpowers (x : G) = D := eq_of_le_of_card_ge (zpowers_le.mpr x.property)
    (by rw [Nat.card_zpowers, hxcard])
  have hlarge : 8 ≤ orderOf (x : G) := by
    rw [Nat.card_zpowers, q.a_order] at hsize
    have h8 : 8 ≤ 2 ^ (q.n + 3) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ q.n + 3)
    omega
  have hxC : (x : G) ∈ zpowers q.a := by
    obtain ⟨i, hi | hi⟩ := q.inner_cover x (hDT x.property) (hDL x.property)
    · rw [hi]; exact zpow_mem (mem_zpowers _) i
    · have hd := orderOf_dvd_of_pow_eq_one (q.reflection_coset_fourth_power hb i)
      rw [← hi] at hd
      have := Nat.le_of_dvd (by decide : 0 < 4) hd
      omega
  apply eq_of_le_of_card_ge _ hsize
  rw [← hDx]
  exact zpowers_le.mpr hxC

end Theory.GroupTheory.CyclicByFourCoordinates

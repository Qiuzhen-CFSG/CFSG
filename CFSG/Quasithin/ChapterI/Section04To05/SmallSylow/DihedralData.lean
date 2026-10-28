module

public import GorensteinWalter.DihedralCore
public import GorensteinWalter.DihedralRotationIndexTwo
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Marked rotation data for the dihedral source branch

The cyclic rotation subgroup has index two and a unique involution. Its
involution is central, and every element outside it is a reflection of order
two. These actual subgroup data are the input to the transfer argument in
Aschbacher–Smith I.4.3, printed pp.416–417.
-/

namespace CFSG.Quasithin.ChapterI.SmallSylow
open Subgroup GorensteinWalter

/-- A genuine dihedral two-group has the cyclic rotation subgroup and central involution used by transfer. -/
public theorem dihedral_rotation_data {T : Type*} [Group T] [Finite T]
    {m : ℕ} (hm : 1 ≤ m) (e : T ≃* DihedralGroup (2 ^ m)) :
    ∃ R : Subgroup T, IsCyclic R ∧ R.index = 2 ∧
      ∃ z : R, orderOf z = 2 ∧ (z : T) ∈ center T ∧
        ∀ v : T, v ∉ R → orderOf v = 2 := by
  let D := DihedralGroup (2 ^ m)
  let C : Subgroup D := zpowers (DihedralGroup.r 1)
  let R := C.map e.symm.toMonoidHom
  have hCcard : Nat.card C = 2 ^ m := by
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hRcyc : IsCyclic R := (e.symm.subgroupMap C).isCyclic.mp inferInstance
  let : IsCyclic R := hRcyc
  have hidx : R.index = 2 := by
    exact (index_map_equiv C e.symm).trans dihedral_rotation_index_two
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (by
    rw [hCcard]; exact dvd_pow_self _ (by omega))
  let z : R := e.symm.subgroupMap C w
  have hz : orderOf z = 2 := ((e.symm.subgroupMap C).orderOf_eq w).trans hw
  have hCcentral : (w : D) ∈ center D := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp w.property
    have hwform : (w : D) = DihedralGroup.r (k : ZMod (2 ^ m)) := by
      rw [← hk, DihedralGroup.r_one_zpow]
    have hsq : (w : D) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one w
      rw [hw] at h
      exact congrArg Subtype.val h
    have hneg : -(k : ZMod (2 ^ m)) = k := by
      have hinv : (w : D)⁻¹ = w := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hsq)
      rw [hwform, DihedralGroup.inv_r] at hinv
      exact DihedralGroup.r.inj hinv
    apply mem_center_iff.mpr
    intro x
    rw [hwform]
    rcases dihedralGroup_cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
    · rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, sub_eq_add_neg, hneg]
  refine ⟨R, hRcyc, hidx, z, hz, ?_, ?_⟩
  · apply mem_center_iff.mpr
    intro x
    apply e.injective
    have hez : e (z : T) = w := e.apply_symm_apply w
    simpa only [map_mul, hez] using mem_center_iff.mp hCcentral (e x)
  · intro v hv
    rcases dihedralGroup_cases (e v) with ⟨i, hi⟩ | ⟨i, hi⟩
    · exfalso
      apply hv
      exact ⟨e v, hi ▸ r_mem_zpowers_r_one i, e.symm_apply_apply v⟩
    · exact (e.orderOf_eq v).symm.trans (hi ▸ DihedralGroup.orderOf_sr i)

end CFSG.Quasithin.ChapterI.SmallSylow

module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.Contracts
public import Theory.GroupTheory.DihedralSemidihedralSquares
public import Theory.ElementaryAbelian.Join

/-!
# The characteristic rotations of the centralizer Sylow subgroup

Transport the canonical rotations through the actual dihedral or semidihedral
model. The centralizer of t is elementary of order at most four, so t lies
outside the rotations; index two then gives generation by the rotations and t.

Adapted from the saved DihedralActions proof work. Source: Aschbacher--Smith,
combined manuscript of 1 March 2004, 16.3.8 and 16.3.12, printed pp.1179--1182.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
open Subgroup
variable {G : Type*} [Group G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

private theorem characteristic_zpowers_transport {S H : Type*} [Group S] [Group H]
    (e : S ≃* H) (a : H) (hc : (zpowers a).Characteristic) :
    (zpowers (e.symm a)).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro f x hx
  change f x ∈ zpowers (e.symm a)
  have hx' : e x ∈ zpowers a := by
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, ?_⟩
    rw [← hk]
    simp only [map_zpow, e.apply_symm_apply]
  let g : H ≃* H := e.symm.trans (f.trans e)
  have hg := characteristic_iff_le_comap.mp hc g hx'
  obtain ⟨k, hk⟩ := hg
  refine ⟨k, ?_⟩
  apply e.injective
  rw [map_zpow]
  simpa [g] using hk

private theorem ambient_rotation {C : Subgroup G} (a : C) (k : ℕ) (hk : 2 ≤ k)
    (ha : orderOf a = 2 ^ k) (hc : (zpowers a).Characteristic)
    (hi : (zpowers a).index = 2) :
    ∃ y : G, zpowers y ≤ C ∧ ((zpowers y).subgroupOf C).Characteristic ∧
      (zpowers y).relIndex C = 2 ∧ ∃ n : ℕ, 2 ≤ n ∧ orderOf y = 2 ^ n := by
  have hm : (zpowers (a : G)).subgroupOf C = zpowers a := by
    rw [show zpowers (a : G) = (zpowers a).map C.subtype by rw [MonoidHom.map_zpowers]; rfl]
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      have : y = x := C.subtype_injective heq
      simpa [this] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨a, zpowers_le.mpr a.property, hm.symm ▸ hc, ?_, k, hk, (orderOf_coe a).trans ha⟩
  change ((zpowers (a : G)).subgroupOf C).index = 2
  rw [hm]
  exact hi

theorem exists_characteristic_index_two_generator (d : Prepared T z t L) :
    ∃ y : G, zpowers y ≤ commutingSylow T L ∧
      ((zpowers y).subgroupOf (commutingSylow T L)).Characteristic ∧
      (zpowers y).relIndex (commutingSylow T L) = 2 ∧
      ∃ n : ℕ, 2 ≤ n ∧ orderOf y = 2 ^ n := by
  rcases d.shape.model with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · let a := e.symm (DihedralGroup.r 1)
    have ha : orderOf a = 2 ^ n := by
      rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    have hc : (zpowers a).Characteristic := characteristic_zpowers_transport e _
      (DihedralGroup.rotations_characteristic
        (lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hn)))
    apply ambient_rotation a n hn ha hc
    have h := (zpowers a).card_mul_index
    rw [Nat.card_zpowers, ha, Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h
    nlinarith [pow_pos (by decide : 0 < (2 : ℕ)) n]
  · let a := e.symm (Semidihedral.standardRotation n hn)
    have ha : orderOf a = 2 ^ (n - 1) := by
      rw [MulEquiv.orderOf_eq, Semidihedral.standardRotation_order]
    have hc : (zpowers a).Characteristic := characteristic_zpowers_transport e _
      (Semidihedral.rotations_characteristic hn _ _
        (Semidihedral.standardRotation_order n hn) (Semidihedral.standardReflection_order n hn)
        (Semidihedral.standard_conjugation n hn) (Semidihedral.standard_generators n hn))
    apply ambient_rotation a (n - 1) (by omega) ha hc
    have h := (zpowers a).card_mul_index
    rw [Nat.card_zpowers, ha, Nat.card_congr e.toEquiv, Semidihedral.standardModel_card] at h
    have hp : 2 ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hp] at h
    nlinarith [pow_pos (by decide : 0 < (2 : ℕ)) (n - 1)]

theorem reflection_not_mem_rotation (d : Prepared T z t L) {y : G}
    (hY : zpowers y ≤ commutingSylow T L)
    (ho : ∃ n : ℕ, 2 ≤ n ∧ orderOf y = 2 ^ n) : t ∉ zpowers y := by
  intro ht
  have hyt : Commute y t := by
    obtain ⟨i, rfl⟩ := ht
    exact Commute.self_zpow y i
  have hzt : Commute z t :=
    (mem_centralizer_singleton_iff.mp
      (d.counterexample.localSetup.sylow_centralizes d.counterexample.mem_commutingSylow.1)).symm
  let : IsElementaryAbelian 2 (zpowers z) := IsElementaryAbelian.zpowers_of_pow_eq_one
    (d.counterexample.localSetup.involution ▸ pow_orderOf_eq_one z)
  let : IsElementaryAbelian 2 (zpowers t) := IsElementaryAbelian.zpowers_of_pow_eq_one
    (d.counterexample.involution ▸ pow_orderOf_eq_one t)
  have hc : zpowers t ≤ centralizer (zpowers z : Set G) := by
    apply zpowers_le.mpr
    rintro x ⟨i, rfl⟩
    exact hzt.zpow_left i
  let : IsElementaryAbelian 2 (zpowers z ⊔ zpowers t : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hc
  have hy : y ∈ zpowers z ⊔ zpowers t := d.shape.centralizer_eq ▸
    ⟨hY (mem_zpowers y), mem_centralizer_singleton_iff.mpr hyt.eq⟩
  have hd := orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian (p := 2) y hy)
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
  obtain ⟨n, hn, he⟩ := ho
  have hlo : 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hn
  omega

theorem rotation_sup_reflection (d : Prepared T z t L) {y : G}
    (hY : zpowers y ≤ commutingSylow T L)
    (hi : (zpowers y).relIndex (commutingSylow T L) = 2)
    (ho : ∃ n : ℕ, 2 ≤ n ∧ orderOf y = 2 ^ n) :
    zpowers y ⊔ zpowers t = commutingSylow T L := by
  have ht := reflection_not_mem_rotation d hY ho
  have ht2 : t * t = 1 := by
    have ht2 : t ^ 2 = 1 := d.counterexample.involution ▸ pow_orderOf_eq_one t
    simpa only [pow_two] using ht2
  apply le_antisymm (sup_le hY (zpowers_le.mpr d.counterexample.mem_commutingSylow))
  intro x hx
  by_cases hxY : x ∈ zpowers y
  · exact mem_sup_left hxY
  · have hm : x * t ∈ zpowers y := by
      exact (mul_mem_iff_of_index_two (show
        ((zpowers y).subgroupOf (commutingSylow T L)).index = 2 from hi)
        (a := ⟨x, hx⟩) (b := ⟨t, d.counterexample.mem_commutingSylow⟩)).mpr
          ⟨fun h => (hxY h).elim, fun h => (ht h).elim⟩
    have hprod := (zpowers y ⊔ zpowers t).mul_mem
      (mem_sup_left hm) (mem_sup_right (mem_zpowers t))
    simpa only [mul_assoc, ht2, mul_one] using hprod

end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation

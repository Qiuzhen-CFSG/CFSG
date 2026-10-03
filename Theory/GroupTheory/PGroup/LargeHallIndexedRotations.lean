module

public import Theory.GroupTheory.PGroup.LargeHallRotationStructure

/-!
# Indexed rotations in large binary Hall factors

The characteristic cyclic rotations in a large dihedral, generalized quaternion,
or semidihedral group have index two and order at least eight. The center has
exponent two. This extension retains the index needed for centralizer counting.

The model calculations adapt the private rotation data in
`LargeHallRotationStructure`; the existing public interface is unchanged.
Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.392, Case 1.
-/

open Subgroup

private theorem index_two_rotation_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (R : Subgroup G) [R.Characteristic] [IsCyclic R]
    (hi : R.index = 2) (hR : 8 ≤ Nat.card R)
    (hZ : ∀ z ∈ center G, z ^ 2 = (1 : G)) :
    ∃ S : Subgroup H, S.Characteristic ∧ IsCyclic S ∧ S.index = 2 ∧
      8 ≤ Nat.card S ∧ ∀ z ∈ center H, z ^ 2 = (1 : H) := by
  let S := R.map (e : G →* H)
  have he := e.subgroupMap R
  refine ⟨S, ?_, he.isCyclic.mp inferInstance, ?_, ?_, ?_⟩
  · apply characteristic_iff_le_comap.mpr
    intro f x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨e.symm (f (e y)), ?_, by simp⟩
    exact characteristic_iff_le_comap.mp inferInstance
      ((e.trans f).trans e.symm) hy
  · simpa [S] using hi
  · change 8 ≤ Nat.card (R.map (e : G →* H))
    rw [← Nat.card_congr he.toEquiv]
    exact hR
  · intro z hz
    obtain ⟨z, rfl⟩ := e.surjective z
    have hz' : z ∈ center G := mem_center_iff.mpr (by
      intro x
      apply e.injective
      simpa only [map_mul] using mem_center_iff.mp hz (e x))
    simpa only [map_pow, map_one] using congrArg e (hZ z hz')

private theorem quaternion_rotation_data {m : ℕ} (hm : 4 ≤ m) :
    ∃ R : Subgroup (QuaternionGroup m), R.Characteristic ∧ IsCyclic R ∧
      R.index = 2 ∧ 8 ≤ Nat.card R ∧
      ∀ z ∈ center (QuaternionGroup m), z ^ 2 = (1 : QuaternionGroup m) := by
  let : NeZero m := ⟨by omega⟩
  let R := zpowers (QuaternionGroup.a 1 : QuaternionGroup m)
  have hcard : Nat.card R = 2 * m := by rw [Nat.card_zpowers, QuaternionGroup.orderOf_a_one]
  refine ⟨R, ?_, inferInstance, ?_, by omega, ?_⟩
  · apply characteristic_iff_le_comap.mpr
    intro f
    apply zpowers_le.mpr
    change f (QuaternionGroup.a 1) ∈ R
    have hord := f.orderOf_eq (QuaternionGroup.a 1)
    cases he : f (QuaternionGroup.a 1) with
    | a i =>
      have h := pow_mem (mem_zpowers (QuaternionGroup.a 1 : QuaternionGroup m)) i.val
      simpa only [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val] using h
    | xa i =>
      rw [he, QuaternionGroup.orderOf_xa, QuaternionGroup.orderOf_a_one] at hord
      omega
  · have h := R.index_mul_card
    rw [hcard, Nat.card_eq_fintype_card, QuaternionGroup.card] at h
    nlinarith
  · exact QuaternionGroup.sq_eq_one_of_mem_center (by omega)

private theorem dihedral_rotation_data {m : ℕ} (hm : 8 ≤ m) :
    ∃ R : Subgroup (DihedralGroup m), R.Characteristic ∧ IsCyclic R ∧
      R.index = 2 ∧ 8 ≤ Nat.card R ∧
      ∀ z ∈ center (DihedralGroup m), z ^ 2 = (1 : DihedralGroup m) := by
  let : NeZero m := ⟨by omega⟩
  let R := zpowers (DihedralGroup.r 1 : DihedralGroup m)
  have hcard : Nat.card R = m := by rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  refine ⟨R, DihedralGroup.rotations_characteristic (by omega), inferInstance,
    ?_, by omega, ?_⟩
  · have h := R.index_mul_card
    rw [hcard, DihedralGroup.nat_card] at h
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < m) h
  · intro z hz
    cases z with
    | r i =>
      have hi : i = -i := by simpa using mem_center_iff.mp hz (DihedralGroup.sr 0)
      simp only [pow_two, DihedralGroup.r_mul_r, DihedralGroup.one_def]
      congr 1
      linear_combination hi
    | sr i => simp only [pow_two, DihedralGroup.sr_mul_self]

private theorem semidihedral_rotation_data {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 4 ≤ n) (hcard : Nat.card G = 2 ^ n) (a b : G)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : closure ({a, b} : Set G) = ⊤) :
    ∃ R : Subgroup G, R.Characteristic ∧ IsCyclic R ∧ R.index = 2 ∧
      8 ≤ Nat.card R ∧ ∀ z ∈ center G, z ^ 2 = (1 : G) := by
  let R := zpowers a
  have hR : Nat.card R = 2 ^ (n - 1) := by rw [Nat.card_zpowers, ha]
  refine ⟨R, Semidihedral.rotations_characteristic hn a b ha hb hconj hgen,
    inferInstance, ?_, ?_, ?_⟩
  · have h := R.index_mul_card
    have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
      omega
    rw [hR, hcard, hp] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ (n - 1)) h
  · rw [hR]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ n - 1)
  · intro z hz
    rw [Semidihedral.center_eq hn a b ha hb hconj hgen] at hz
    obtain ⟨i, rfl⟩ := hz
    have hs : (a ^ (2 ^ (n - 2))) ^ 2 = 1 := by
      rw [← pow_mul, ← pow_succ, show n - 2 + 1 = n - 1 by omega, ← ha]
      exact pow_orderOf_eq_one a
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs, one_zpow]

/-- The cyclic rotations in a large noncyclic binary Hall factor have index two,
and every central element has square one. -/
public theorem IsBinaryHallFactor.exists_index_two_large_rotation {D : Type*} [Group D] [Finite D]
    (hD : IsBinaryHallFactor D) (hnc : ¬ IsCyclic D) (hlarge : 16 ≤ Nat.card D) :
    ∃ R : Subgroup D, R.Characteristic ∧ IsCyclic R ∧ R.index = 2 ∧
      8 ≤ Nat.card R ∧ ∀ z ∈ center D, z ^ 2 = (1 : D) := by
  rcases hD with hcyc | ⟨n, hn, ⟨e⟩⟩ | ⟨m, ⟨e⟩⟩ | ⟨n, hn, hc, a, b, ha, hb, hr, hg⟩
  · exact (hnc hcyc).elim
  · have hc : Nat.card D = 4 * 2 ^ (n - 2) := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    obtain ⟨R, hRc, hRcyc, hi, hR, hZ⟩ := quaternion_rotation_data (by omega : 4 ≤ 2 ^ (n - 2))
    let : R.Characteristic := hRc
    let : IsCyclic R := hRcyc
    exact index_two_rotation_map e.symm R hi hR hZ
  · have hc : Nat.card D = 2 * m := (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
    obtain ⟨R, hRc, hRcyc, hi, hR, hZ⟩ := dihedral_rotation_data (by omega : 8 ≤ m)
    let : R.Characteristic := hRc
    let : IsCyclic R := hRcyc
    exact index_two_rotation_map e.symm R hi hR hZ
  · exact semidihedral_rotation_data hn hc a b ha hb hr hg

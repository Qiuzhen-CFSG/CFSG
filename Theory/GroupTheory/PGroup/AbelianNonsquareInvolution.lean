module

public import Theory.GroupTheory.PGroup.AbelianRankTwoHomocyclic
public import Theory.GroupTheory.PGroup.AbelianOmega
public import Theory.GroupAction.Quotient

/-!
# A cyclic complement to a specified nonsquare involution

For a finite abelian two-group with first omega subgroup of order four, quotienting
by the specified involution leaves a cyclic group when that involution is not a
square. A lift of a quotient generator gives the required cyclic complement;
nontrivial intersection would make the specified involution a square. This is
the rank-two complement step in MacWilliams, *Trans. AMS* 150 (1970), §3(iv),
printed p. 368 (PDF p. 24).
-/

open scoped IsMulCommutative
open Subgroup

namespace IsPGroup

public theorem exists_cyclic_complement_of_nonsquare_involution
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (hA : IsPGroup 2 A) (hfour : Nat.card (omega₁ A (p := 2)) = 4)
    (z : A) (hz : orderOf z = 2) (hns : ¬ ∃ a : A, a ^ 2 = z) :
    ∃ b : A, Subgroup.zpowers b ⊔ Subgroup.zpowers z = ⊤ ∧
      Disjoint (Subgroup.zpowers b) (Subgroup.zpowers z) := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  let Z : Subgroup A := Subgroup.zpowers z
  let E : Subgroup A := omega₁ A (p := 2)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.omega₁_of_isMulCommutative A
  let q : A →* (A ⧸ Z) := QuotientGroup.mk' Z
  have hzsq : z ^ 2 = 1 := by simpa [hz] using pow_orderOf_eq_one z
  have hzpow_even (j : ℤ) : z ^ (2 * j) = 1 := by
    apply (orderOf_dvd_iff_zpow_eq_one).1
    rw [hz]
    exact ⟨j, rfl⟩
  have hzpow_odd (j : ℤ) : z ^ (2 * j + 1) = z := by
    rw [zpow_add_one, hzpow_even, one_mul]
  have hzE : z ∈ E := by
    exact subset_closure (by simpa using hzsq)
  have hZcard : Nat.card Z = 2 := by
    simp [Z, Nat.card_zpowers, hz]
  have hmap_le : E.map q ≤ omega₁ (A ⧸ Z) (p := 2) := by
    apply Subgroup.map_le_iff_le_comap.mpr
    intro x hx
    apply Subgroup.subset_closure
    change q x ^ 2 = 1
    rw [← map_pow]
    rw [elemPow_eq_one_of_isElementaryAbelian x hx (p := 2) (A := E), map_one]
  let : IsElementaryAbelian 2 (omega₁ (A ⧸ Z) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  have hmap_ge : omega₁ (A ⧸ Z) (p := 2) ≤ E.map q := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z y
    have hxZ : x ^ 2 ∈ Z := by
      apply (QuotientGroup.eq_one_iff (N := Z) (x ^ 2)).mp
      change q (x ^ 2) = 1
      rw [map_pow]
      exact elemPow_eq_one_of_isElementaryAbelian (q x) hy (p := 2)
        (A := omega₁ (A ⧸ Z) (p := 2))
    obtain ⟨k, hk⟩ := hxZ
    have hkpow : x ^ 2 = z ^ k := hk.symm
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · have hxeq : x ^ 2 = 1 := by
        exact hkpow.trans (hzpow_even j)
      have hxE : x ∈ E := subset_closure (by simpa using hxeq)
      exact ⟨x, hxE, rfl⟩
    · have hxsq : x ^ 2 = z := by
        exact hkpow.trans (hzpow_odd j)
      exact (hns ⟨x, hxsq⟩).elim
  have hEq : omega₁ (A ⧸ Z) (p := 2) = E.map q := le_antisymm hmap_ge hmap_le
  have hcardquot : Nat.card (E ⧸ Z.subgroupOf E) = 2 := by
    have hfour' := hfour
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf E)] at hfour'
    have hZsub : Nat.card (Z.subgroupOf E) = 2 := by
      have hZE : Z ≤ E := Subgroup.zpowers_le.mpr hzE
      rw [Nat.card_congr (Z.subgroupOfEquivOfLe hZE).toEquiv]
      exact hZcard
    rw [hZsub] at hfour'
    omega
  have hcardomega : Nat.card (omega₁ (A ⧸ Z) (p := 2)) ≤ 2 := by
    rw [hEq, natCard_map_mk'_eq E Z, hcardquot]
  have hqcyc : IsCyclic (A ⧸ Z) :=
    IsPGroup.isCyclic_of_card_omega_one_le_two (hA.to_quotient Z) hcardomega
  obtain ⟨qgen, hqgen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hqcyc
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective Z qgen
  have hqtop : Subgroup.zpowers (q b) = ⊤ := by rw [hb]; exact hqgen
  have hsup : Subgroup.zpowers b ⊔ Z = ⊤ := by
    rw [← MonoidHom.map_zpowers q b] at hqtop
    have hker : q.ker = Z := by
      ext x
      simp [q, Z]
    simpa only [Subgroup.comap_map_eq, hker, Subgroup.comap_top] using
      (congrArg (Subgroup.comap q) hqtop :
        Subgroup.comap q (Subgroup.map q (Subgroup.zpowers b)) = ⊤)
  refine ⟨b, hsup, ?_⟩
  apply Subgroup.disjoint_def.mpr
  intro x hxB hxZ
  have hxZ' : x = 1 ∨ x = z := by
    obtain ⟨k, hk⟩ := hxZ
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      exact hk.symm.trans (hzpow_even j)
    · right
      exact hk.symm.trans (hzpow_odd j)
  rcases hxZ' with hx1 | hxz
  · exact hx1
  · obtain ⟨k, hk⟩ := hxB
    have hkz : b ^ k = z := hk.trans hxz
    have hqk : (q b) ^ k = 1 := by
      have hh := congrArg q hkz
      rw [map_zpow] at hh
      rw [hh]
      exact (QuotientGroup.eq_one_iff (N := Z) z).2 (Subgroup.mem_zpowers _)
    have hcardq : orderOf (q b) = Nat.card (A ⧸ Z) := by
      rw [orderOf_eq_card_of_forall_mem_zpowers (fun y => by rw [hqtop]; trivial)]
    have h4div : 4 ∣ Nat.card A := by
      have hd : Nat.card E ∣ Nat.card A := by
        simpa using
          (Subgroup.card_dvd_of_le (H := E) (show E ≤ (⊤ : Subgroup A) from le_top))
      rwa [hfour] at hd
    have hprod : 2 * Z.index = Nat.card A := by
      simpa [hZcard] using Subgroup.card_mul_index Z
    have hindex_even : 2 ∣ Z.index := by
      obtain ⟨t, ht⟩ := h4div
      refine ⟨t, ?_⟩
      rw [← hprod] at ht
      have hh : 2 * Z.index = 4 * t := by omega
      have : Z.index = 2 * t := by omega
      exact this
    have hqcard_even : 2 ∣ orderOf (q b) := by
      rw [hcardq, ← Subgroup.index_eq_card]
      exact hindex_even
    have hdivZ : (orderOf (q b) : ℤ) ∣ k :=
      (orderOf_dvd_iff_zpow_eq_one).2 hqk
    have hqcard_evenZ : (2 : ℤ) ∣ (orderOf (q b) : ℤ) := by exact_mod_cast hqcard_even
    have hkevenZ : (2 : ℤ) ∣ k := dvd_trans hqcard_evenZ hdivZ
    exfalso
    apply hns
    obtain ⟨a, ha⟩ := (Even.isSquare_zpow ((even_iff_two_dvd).2 hkevenZ) b)
    refine ⟨a, ?_⟩
    rw [hkz] at ha
    simpa [pow_two, mul_comm] using ha.symm

end IsPGroup

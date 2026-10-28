module

public import Theory.GroupTheory.QuaternionPresentation
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Quaternion eight from two distinct cyclic subgroups of order four

In a nonabelian group of order eight, two elements of order four from
distinct cyclic subgroups generate the group. Each cyclic subgroup has
index two. Conjugation therefore inverts a generator of the first one,
and the two generators have the same square. The quaternion presentation
then supplies an actual multiplicative equivalence with Q₈.

This is the recognition step in Aschbacher–Smith J.2.3(7), printed p.434,
combined manuscript of 1 March 2004. Construction of the cyclic subgroups
and exclusion of the abelian alternative are separate inputs.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace QuaternionGroup
variable {P : Type*} [Group P] [Finite P]

theorem equiv_of_card_eight_two_cyclic_four
    (hcard : Nat.card P = 8) (hnoncomm : ¬ IsMulCommutative P)
    (c d : P) (hc : orderOf c = 4) (hd : orderOf d = 4)
    (hout : d ∉ zpowers c) : Nonempty (P ≃* QuaternionGroup 2) := by
  classical
  let A := zpowers c
  have hi : A.index = 2 := by
    have h := A.index_mul_card
    rw [Nat.card_zpowers, hc, hcard] at h
    omega
  let _ : A.Normal := normal_of_index_eq_two hi
  let U := closure ({c,d} : Set P)
  have hcU : c ∈ U := subset_closure (by simp)
  have hdU : d ∈ U := subset_closure (by simp)
  have hAU : A ≤ U := zpowers_le.mpr hcU
  have hgen : U = ⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x ∈ A
    · exact hAU hx
    · have hdx : d * x ∈ A := (mul_mem_iff_of_index_two hi).mpr ⟨
        fun hh => (hout hh).elim, fun hh => (hx hh).elim⟩
      simpa using U.mul_mem (U.inv_mem hdU) (hAU hdx)
  have hnc : ¬ Commute c d := by
    intro hcd
    have hU : IsMulCommutative U := isMulCommutative_closure (by
      intro x hx y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact hcd.eq
      · exact hcd.eq.symm
      · rfl)
    let _ := hU
    apply hnoncomm
    refine { is_comm := ⟨fun x y => ?_⟩ }
    have hx : x ∈ U := hgen ▸ mem_top x
    have hy : y ∈ U := hgen ▸ mem_top y
    exact congrArg (fun z : U => (z : P)) (mul_comm ⟨x,hx⟩ ⟨y,hy⟩)
  have hc4 : c ^ 4 = 1 := hc ▸ pow_orderOf_eq_one c
  have hd4 : d ^ 4 = 1 := hd ▸ pow_orderOf_eq_one d
  have hc2 : c ^ 2 ≠ 1 := by
    intro hh
    have := orderOf_dvd_of_pow_eq_one hh
    norm_num [hc] at this
  have hd2 : d ^ 2 ≠ 1 := by
    intro hh
    have := orderOf_dvd_of_pow_eq_one hh
    norm_num [hd] at this
  have hc3 : c ^ 3 = c⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact hc4
  have hsq : d ^ 2 = c ^ 2 := by
    have hm := sq_mem_of_index_two hi d
    change d ^ 2 ∈ zpowers c at hm
    rw [mem_zpowers_iff_mem_range_orderOf] at hm
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hm
    have hk4 : k < 4 := by simpa [hc] using hk
    have hpow : (d ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hd4
    interval_cases k
    · exact (hd2 (by simpa using he.symm)).elim
    · have hh : c ^ 2 = 1 := by simpa [← he] using hpow
      exact (hc2 hh).elim
    · exact he.symm
    · have hh : c⁻¹ ^ 2 = 1 := by simpa [← he, hc3] using hpow
      exact (hc2 (by simpa only [inv_pow, inv_eq_one] using hh)).elim
  have hinv : d * c * d⁻¹ = c⁻¹ := by
    have hm : d * c * d⁻¹ ∈ A := (inferInstance : A.Normal).conj_mem c (mem_zpowers c) d
    change d * c * d⁻¹ ∈ zpowers c at hm
    rw [mem_zpowers_iff_mem_range_orderOf] at hm
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hm
    have hk4 : k < 4 := by simpa [hc] using hk
    have ho : orderOf (d * c * d⁻¹) = 4 := (MulAut.conj d).orderOf_eq c |>.trans hc
    interval_cases k
    · have hh : d * c * d⁻¹ = 1 := by simpa using he.symm
      rw [hh, orderOf_one] at ho
      omega
    · have hh : d * c * d⁻¹ = c := by simpa using he.symm
      exact (hnc ((mul_inv_eq_iff_eq_mul.mp hh).symm)).elim
    · have hh : (d * c * d⁻¹) ^ 2 = 1 := by rw [← he, ← pow_mul]; exact hc4
      have hdiv := orderOf_dvd_of_pow_eq_one hh
      norm_num [ho] at hdiv
    · exact he.symm.trans hc3
  exact quaternionGroup_equiv_of_presentation (by decide) c d hc hsq hinv hgen hcard
end QuaternionGroup

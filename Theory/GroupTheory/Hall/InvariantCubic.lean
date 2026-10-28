module
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# An invariant cubic for an odd actor

If an odd-order element normalizes a solvable subgroup X of order 2^n·3,
then it normalizes a subgroup of order three in X. Place the cyclic actor
in an odd Hall subgroup of its solvable product with X, and restrict that
Hall subgroup to X. The restriction has odd order dividing 3 and index
prime to 3, so it has order exactly three.

This supplies the invariant Sylow choice in Aschbacher–Smith, *The
Classification of Quasithin Groups*, 3.3.31, printed p.602. All normalizers
and subgroup products remain in the original ambient group.
-/

public section
open Subgroup
namespace Subgroup.OddHall
variable {G : Type*} [Group G] [Finite G]

/-- An odd actor normalizing a solvable group of order 2^n·3 normalizes
an actual subgroup of order three in it. -/
theorem exists_invariant_cubic_of_odd_actor (X : Subgroup G)
    (hsolv : Group.IsSolvable X) {n : ℕ} (hcard : Nat.card X = 2 ^ n * 3)
    {d : G} (ho : Odd (orderOf d)) (hd : d ∈ normalizer (X : Set G)) :
    ∃ B : Subgroup G, B ≤ X ∧ Nat.card B = 3 ∧ d ∈ normalizer (B : Set G) := by
  let D := zpowers d
  have hDX : D ≤ normalizer (X : Set G) := zpowers_le.mpr hd
  let : Group.IsSolvable D := Group.isSolvable_of_comm (isMulCommutative_iff.mp inferInstance)
  let J := X ⊔ D
  let : Group.IsSolvable X := hsolv
  have hJ : Group.IsSolvable J := Group.isSolvable_sup_of_normalizes X D hDX
  have hDodd : Odd (Nat.card D) := by simpa only [D, Nat.card_zpowers] using ho
  obtain ⟨C, hDC, hCJ, hhall⟩ := exists_hall_containing_odd J D hJ le_sup_right hDodd
  have hJX : J ≤ normalizer (X : Set G) := sup_le X.le_normalizer hDX
  have hh := hall_restrict_of_normalizes hhall hCJ (show X ≤ J from le_sup_left)
    (hCJ.trans hJX)
  let B := C ⊓ X
  have hBX : B ≤ X := inf_le_right
  have hc : Nat.card (C.subgroupOf X) = Nat.card B := by
    rw [← inf_subgroupOf_right C X]
    exact Nat.card_congr (subgroupOfEquivOfLe hBX).toEquiv
  have hodd : ¬ 2 ∣ Nat.card B := by
    intro he
    apply hh.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ (hc.symm ▸ he)
    rfl
  have hdiv : Nat.card B ∣ 3 := by
    have hdvd := card_dvd_of_le hBX
    rw [hcard] at hdvd
    exact ((Nat.prime_two.coprime_iff_not_dvd.mpr hodd).symm.pow_right n).dvd_of_dvd_mul_left hdvd
  have hthree : 3 ∣ Nat.card B := by
    have h3X : 3 ∣ Nat.card X := by rw [hcard]; exact dvd_mul_left _ _
    rw [← (C.subgroupOf X).card_mul_index, hc] at h3X
    rcases Nat.prime_three.dvd_mul.mp h3X with he | he
    · exact he
    · exact False.elim (hh.p_in_pi_of_p_dvd_index ⟨3, Nat.prime_three⟩ he (by change (3 : ℕ) ≠ 2; decide))
  refine ⟨B, hBX, Nat.dvd_antisymm hdiv hthree, ?_⟩
  have hdC : d ∈ C := hDC (mem_zpowers d)
  exact inf_normalizer_le_normalizer_inf ⟨C.le_normalizer hdC, hd⟩
end Subgroup.OddHall

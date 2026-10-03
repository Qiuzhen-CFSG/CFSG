module

public import Stellmacher.Recognition.LyonsU3Four.Basic
public import Theory.GroupTheory.PGroup.InvertingInvolution
public import BenderSuzuki.PFAppendixIII.Basic

/-!
# Elementary consequences of Lyons's intrinsic Sylow hypotheses

The square-generated subgroup is the elementary abelian center, so the
Sylow subgroup has exponent four. All involutions are central in it.
Consequently no ambient element of order four is inverted by an involution.
This proves the failure of strong reality in Lemma 1(b), independently of
the fusion and odd-core quotient calculations.

Source: Lyons, *A Characterization of the Group U₃(4)*, pp. 372–373.
-/

namespace Stellmacher.Recognition.LyonsU3Four

public theorem square_mem_center {G : Type*} [Group G]
    (S : Sylow 2 G) (h : SylowStructure S) (s : S) :
    s ^ 2 ∈ Subgroup.center S := by
  rw [h.center_eq_squares]
  exact Subgroup.subset_closure ⟨s, rfl⟩

public theorem pow_four_eq_one {G : Type*} [Group G]
    (S : Sylow 2 G) (h : SylowStructure S) (s : S) : s ^ 4 = 1 := by
  let _ := h.center_elementary
  have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) (s ^ 2)
    (square_mem_center S h s)
  simpa only [← pow_mul] using hs

public theorem square_one_mem_center {G : Type*} [Group G]
    (S : Sylow 2 G) (h : SylowStructure S) {s : S} (hs : s ^ 2 = 1) :
    s ∈ Subgroup.center S := by
  rw [h.center_eq_omega]
  apply Subgroup.subset_closure
  simpa using hs

/-- The noncentral Sylow elements are exactly the elements of order four. -/
public theorem order_four_iff_not_mem_center {G : Type*} [Group G]
    (S : Sylow 2 G) (h : SylowStructure S) (s : S) :
    orderOf s = 4 ↔ s ∉ Subgroup.center S := by
  constructor
  · intro hs hcenter
    let _ := h.center_elementary
    have hs2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) s hcenter
    have hdvd := orderOf_dvd_of_pow_eq_one hs2
    rw [hs] at hdvd
    norm_num at hdvd
  · intro hs
    have hnot : s ^ (2 ^ 1) ≠ 1 := by
      intro heq
      exact hs (square_one_mem_center S h (by simpa using heq))
    exact orderOf_eq_prime_pow hnot (pow_four_eq_one S h s)

/-- The strong-reality obstruction holds for every order-four element of
the ambient group, with no simplicity or odd-core hypothesis. -/
public theorem order_four_not_inverted_by_square_one
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (h : SylowStructure S)
    {t u : G} (ht : orderOf t = 4) (hu : u ^ 2 = 1) :
    u * t * u⁻¹ ≠ t⁻¹ := by
  intro hinv
  have ht4 : t ^ (2 ^ 2) = 1 := by
    change t ^ 4 = 1
    rw [← ht]
    exact pow_orderOf_eq_one t
  have ht2 := S.square_eq_one_of_inverted_by_square_one
    (fun _ hs => square_one_mem_center S h hs) ht4 hu hinv
  have hdvd := orderOf_dvd_of_pow_eq_one ht2
  rw [ht] at hdvd
  norm_num at hdvd

/-- Lemma 1(b), the failure of strong reality, in the existing product-of-two-
involutions interface. -/
public theorem order_four_not_stronglyReal
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (h : SylowStructure S)
    {t : G} (ht : orderOf t = 4) :
    ¬ BenderSuzuki.PFAppendixIII.IsStronglyReal t := by
  rintro ⟨u, v, hu, hv, rfl⟩
  apply order_four_not_inverted_by_square_one S h ht hu.sq_eq_one
  rw [mul_inv_rev, hu.inv_eq_self, hv.inv_eq_self]
  have huu : u * u = 1 := by simpa only [pow_two] using hu.sq_eq_one
  rw [← mul_assoc u u v, huu, one_mul]

end Stellmacher.Recognition.LyonsU3Four

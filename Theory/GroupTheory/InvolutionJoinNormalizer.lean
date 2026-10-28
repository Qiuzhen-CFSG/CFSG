module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic

/-!
# Normalizing a subgroup extended by an exterior involution

Suppose A lies in F, u is an involution outside F normalizing A, and x is
an element of F normalizing A. Then x normalizes the subgroup A⟨u⟩ exactly
when its displacement under u belongs to A. The proof retains the subgroup
join: its elements lie in A or in Au, and conjugating u cannot land in A
because u lies outside F.

This is the normalizer-to-quotient bridge in GLS4, Chapter 2, the definition
of U before Lemma 13.4. No ambient normality of A or F is assumed.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
open scoped Pointwise

/-- The subgroup-join normalizer is detected by the literal involution displacement. -/
public theorem mem_normalizer_join_involution_iff (A F : Subgroup G) (u x : G)
    (hAF : A ≤ F) (huF : u ∉ F) (hu2 : u ^ 2 = 1)
    (huA : u ∈ normalizer (A : Set G))
    (hxF : x ∈ F) (hxA : x ∈ normalizer (A : Set G)) :
    x ∈ normalizer ((A ⊔ zpowers u : Subgroup G) : Set G) ↔
      u * x * u⁻¹ * x⁻¹ ∈ A := by
  classical
  have hu1 : u ≠ 1 := fun he => huF (he ▸ F.one_mem)
  have ho : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have hcases (v : G) (hv : v ∈ A ⊔ zpowers u) : v ∈ A ∨ v * u⁻¹ ∈ A := by
    have hs := coe_mul_of_right_le_normalizer_left A (zpowers u) (zpowers_le.mpr huA)
    rw [← SetLike.mem_coe, hs] at hv
    obtain ⟨a, ha, b, hb, rfl⟩ := hv
    change b ∈ zpowers u at hb
    rw [mem_zpowers_iff_mem_range_orderOf, ho] at hb
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hb
    have hk2 : k < 2 := Finset.mem_range.mp hk
    interval_cases k
    · exact Or.inl (by simpa using ha)
    · exact Or.inr (by simpa using ha)
  constructor
  · intro hx
    have hxU := (mem_normalizer_iff.mp hx u).mp (mem_sup_right (mem_zpowers u))
    rcases hcases _ hxU with hbad | hgood
    · have hh := F.mul_mem (F.mul_mem (F.inv_mem hxF) (hAF hbad)) hxF
      have hu : u ∈ F := by simpa [mul_assoc] using hh
      exact (huF hu).elim
    · have hh := A.inv_mem hgood
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using hh
  · intro hdelta
    let K : Subgroup G := A ⊔ zpowers u
    have hxu : x * u * x⁻¹ ∈ K := by
      have hh := K.mul_mem (show (u * x * u⁻¹ * x⁻¹)⁻¹ ∈ K from
        mem_sup_left (A.inv_mem hdelta)) (show u ∈ K from mem_sup_right (mem_zpowers u))
      simpa [mul_assoc] using hh
    apply mem_normalizer_fintype
    have hle : K ≤ K.comap (MulAut.conj x).toMonoidHom := by
      apply sup_le
      · intro a ha
        exact mem_sup_left ((mem_normalizer_iff.mp hxA a).mp ha)
      · exact zpowers_le.mpr hxu
    exact fun g hg => hle hg

end Subgroup

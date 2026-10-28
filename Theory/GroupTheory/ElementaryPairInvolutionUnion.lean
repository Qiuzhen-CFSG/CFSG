module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
/-!
# Involutions and elementary subgroups of an elementary pair

Write every element of R as uv with u∈U and v∈V. If uv is an involution,
u and v commute. When each v outside U fixes only U∩V in U, this puts
uv in one factor. A subgroup contained in the union of two subgroups is
contained in one of them.

Source application: Aschbacher–Smith, Lemma 2.4.8(7), printed p.531.
-/
public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

theorem elementary_pair_involution_union
    (R U V : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hgen : U ⊔ V = R) (hVU : V ≤ normalizer (U : Set G))
    (hfix : ∀ v ∈ V, v ∉ U → ∀ u ∈ U, Commute v u → u ∈ V) :
    ∀ r ∈ R, r^2=1 → r ∈ U ∨ r ∈ V := by
  intro r hr hr2
  have hp : r ∈ (U : Set G) * (V : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left U V hVU,hgen]
    exact hr
  obtain ⟨u,hu,v,hv,rfl⟩ := hp
  by_cases hvU : v ∈ U
  · exact Or.inl (U.mul_mem hu hvU)
  · have hu2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu
    have hv2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv
    have hui : u⁻¹=u := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hu2)
    have hvi : v⁻¹=v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hv2)
    have huvi : (u*v)⁻¹=u*v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hr2)
    have hc : Commute v u := by
      change v*u=u*v
      simpa only [mul_inv_rev,hui,hvi] using huvi
    exact Or.inr (V.mul_mem (hfix v hv hvU u hu hc) hv)

theorem le_one_of_elementwise_union (A U V : Subgroup G)
    (h : ∀ a ∈ A, a ∈ U ∨ a ∈ V) : A ≤ U ∨ A ≤ V := by
  by_cases hU : A ≤ U
  · exact Or.inl hU
  · obtain ⟨u,huA,huU⟩ := SetLike.not_le_iff_exists.mp hU
    have huV := (h u huA).resolve_left huU
    right
    intro v hvA
    rcases h v hvA with hvU | hvV
    · rcases h (u*v) (A.mul_mem huA hvA) with huvU | huvV
      · exact False.elim (huU ((U.mul_mem_cancel_right hvU).mp huvU))
      · exact (V.mul_mem_cancel_left huV).mp huvV
    · exact hvV
end Subgroup

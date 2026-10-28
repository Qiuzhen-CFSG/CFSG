module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Sylow

/-!
# Intersections of the fixed Hall--Janko Sylow subgroups with the local factors

The inner Sylow subgroup lies in both factors. In the extension, its image
is exactly the intersection of the outer Sylow subgroup with the whole inner
carrier: the other coset is odd. This determines both local Sylow intersections
without replacing either whole Borel by a two-subgroup.
Source: Aschbacher--Smith F.1.1 and F.1.12(I)(10)--(11), pp.259 and 263.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic
open Seed PairNormalizer
open scoped Pointwise

theorem s_le_L (i : Fin 2) : s ≤ L i := by
  fin_cases i
  · exact s_le_l₁
  · exact s_le_l₂

theorem s_inf_L (i : Fin 2) : s ⊓ L i = s := inf_eq_left.mpr (s_le_L i)

private theorem outer_power_cases {x : Extension} (hx : x ∈ Subgroup.zpowers outerElement) :
    x = 1 ∨ x = outerElement := by
  classical
  have htne : outerElement ≠ 1 := fun h => outerElement_not_mem_range (h ▸ intoExtension.range.one_mem)
  have ho : orderOf outerElement = 2 := orderOf_eq_prime outerElement_sq htne
  rw [(isOfFinOrder_of_finite outerElement).mem_zpowers_iff_mem_range_orderOf, ho] at hx
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  have hi2 := Finset.mem_range.mp hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · exact Or.inl (by simpa using hix.symm)
  · exact Or.inr (by simpa using hix.symm)

/-- The outer coset contributes no element of the original carrier. -/
theorem outerS_inf_range : outerS ⊓ intoExtension.range = s.map intoExtension := by
  apply le_antisymm
  · intro x hx
    have hp : x ∈ (s.map intoExtension : Set Extension) * (Subgroup.zpowers outerElement : Set Extension) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _
        (Subgroup.zpowers_le.mpr outerElement_normalizes_s)]
      exact hx.1
    obtain ⟨y, hy, t, ht, hyt⟩ := hp
    rcases outer_power_cases ht with rfl | rfl
    · have he : y = x := by simpa only [mul_one] using hyt
      exact he ▸ hy
    · have he : outerElement ∈ intoExtension.range := by
        have h := intoExtension.range.mul_mem
          (intoExtension.range.inv_mem ((s.map_le_range intoExtension) hy)) hx.2
        rw [← hyt, inv_mul_cancel_left] at h
        exact h
      exact (outerElement_not_mem_range he).elim
  · exact le_inf le_sup_left (s.map_le_range intoExtension)

/-- Both source local Sylows in the extension are the image of the inner Sylow. -/
theorem outerS_inf_outerL (i : Fin 2) : outerS ⊓ outerL i = s.map intoExtension := by
  apply le_antisymm
  · calc
      outerS ⊓ outerL i ≤ outerS ⊓ intoExtension.range :=
        inf_le_inf_left _ ((L i).map_le_range intoExtension)
      _ = s.map intoExtension := outerS_inf_range
  · exact le_inf le_sup_left (Subgroup.map_mono (s_le_L i))

end Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic

module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core
/-! The center of the first involution centralizer has order two. Its
nontrivial element is the marked generator a. Every ambient central element
therefore equals one or a, and the latter is excluded by the certified
noncommutation of a and b. This proves centerlessness without a simplicity
or Schur-multiplier premise.

Source application: the inner-action escape for Aschbacher--Smith 2.4.25,
printed p.543; the local centralizer calculation is GLS3, Table 5.3i. -/
public section
namespace Janko4
open Subgroup
/-- The actual matrix carrier has trivial center, using the center of its
first involution centralizer and the noncommuting standard generators. -/
theorem model_center_eq_bot : center Model = ⊥ := by
  classical
  apply le_bot_iff.mp
  intro x hx
  let C := InvolutionCentralizers.First.centralizer
  have haC : a ∈ C := mem_centralizer_singleton_iff.mpr rfl
  let t : C := ⟨a,haC⟩
  have ht : t ∈ center C := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp y.property
  have ho : orderOf t = 2 := by
    rw [←orderOf_injective C.subtype C.subtype_injective]
    exact orderOf_a
  have hz : center C = zpowers t := by
    symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr ht)
    rw [InvolutionCentralizers.First.centralizer_center_card,Nat.card_zpowers,ho]
  have hxC : x ∈ C := mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hx a).symm
  have hxc : (⟨x,hxC⟩ : C) ∈ center C := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp hx y)
  rw [hz,mem_zpowers_iff_mem_range_orderOf,ho] at hxc
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hxc
  have hn' : n = 0 ∨ n = 1 := by
    have hlt := Finset.mem_range.mp hn
    omega
  rcases hn' with rfl | rfl
  · exact mem_bot.mpr (by simpa using congrArg Subtype.val he.symm)
  · have hexa : x = a := by simpa only [pow_one] using congrArg Subtype.val he.symm
    subst x
    exact (a_mul_b_ne_b_mul_a (mem_center_iff.mp hx b).symm).elim
end Janko4

module
public import Mathlib.Order.Atoms
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Maximal intersections with normal supplements

If a subgroup supplements a normal subgroup and its intersection with that
normal subgroup is maximal there, it is maximal in the whole group.
The proof decomposes each element using the normal supplement; an overgroup
with unchanged intersection is unchanged.
Source application: Aschbacher--Smith, 10.2.9, printed pp.752--753.
-/

public section
open Subgroup
namespace Subgroup
/-- Maximality of an intersection with a normal supplement lifts to the group. -/
theorem isCoatom_of_subgroupOf_normal_supplement {G : Type*} [Group G]
    (A B : Subgroup G) [A.Normal] (hsup : A ⊔ B = ⊤)
    (hmax : IsCoatom (B.subgroupOf A)) : IsCoatom B := by
  refine ⟨?_,?_⟩
  · intro h
    apply hmax.1
    rw [h]
    exact comap_top _
  · intro K hK
    have hs : B.subgroupOf A < K.subgroupOf A := by
      apply lt_iff_le_not_ge.mpr
      refine ⟨comap_mono hK.le,?_⟩
      intro h
      apply hK.not_ge
      intro x hx
      obtain ⟨a,ha,b,hb,rfl⟩ := mem_sup_of_normal_left.mp (hsup.symm ▸ mem_top x)
      have haK : a ∈ K := by
        have hh := K.mul_mem hx (K.inv_mem (hK.le hb))
        simpa only [mul_inv_cancel_right] using hh
      exact B.mul_mem (h (show (⟨a,ha⟩ : A) ∈ K.subgroupOf A from haK)) hb
    have he := hmax.2 _ hs
    apply top_unique
    rw [←hsup]
    exact sup_le (fun a ha => show a ∈ K from
      (show (⟨a,ha⟩ : A) ∈ K.subgroupOf A from he.symm ▸ mem_top _)) hK.le
end Subgroup

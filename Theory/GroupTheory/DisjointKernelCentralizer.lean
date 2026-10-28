module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Exact centralizer lifting for a normal subgroup disjoint from the kernel

A commutator trivial in the image lies in the kernel. Normality places it
in the given subgroup as well, so disjointness makes it trivial. Therefore
the whole image centralizer pulls back exactly. A surjective map then lifts
any image element, and its order must divide a common power bound on an
isomorphic centralizer upstairs.

This repairs the abelian-core centralizer step of Aschbacher--Smith 2.5.21,
printed p.565, by using an exponent contradiction with the maximal rotation.
-/

public section
namespace Subgroup
open scoped commutatorElement
variable {G Q : Type*} [Group G] [Group Q]

/-- A normal subgroup disjoint from a kernel has its centralizer pulled back exactly. -/
theorem centralizer_eq_comap_of_disjoint_kernel
    (f : G →* Q) (X : Subgroup G) [X.Normal] (hd : Disjoint X f.ker) :
    centralizer (X : Set G) = (centralizer (X.map f : Set Q)).comap f := by
  apply le_antisymm
  · intro a ha
    rintro _ ⟨x, hx, rfl⟩
    simpa only [map_mul] using congrArg f (ha x hx)
  · intro a ha x hx
    have hk : ⁅a, x⁆ ∈ f.ker := by
      change f ⁅a, x⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (ha (f x) (mem_map_of_mem f hx)).symm
    have hm : ⁅a, x⁆ ∈ X := by
      exact X.mul_mem ((inferInstance : X.Normal).conj_mem x hx a) (X.inv_mem hx)
    exact (commutatorElement_eq_one_iff_mul_comm.mp (disjoint_def.mp hd hm hk)).symm

/-- A conjugate centralizer cannot lift an element whose order exceeds its power bound. -/
theorem centralizer_power_obstruction
    (f : G →* Q) (hf : Function.Surjective f)
    (C X : Subgroup G) [X.Normal] (hd : Disjoint X f.ker)
    (e : centralizer (C : Set G) ≃* centralizer (X : Set G))
    (m : ℕ) (hpow : ∀ a ∈ centralizer (C : Set G), a ^ m = 1)
    (r : Q) (hr : r ∈ centralizer (X.map f : Set Q)) (ho : ¬ orderOf r ∣ m) : False := by
  obtain ⟨a, ha⟩ := hf r
  have hac : a ∈ centralizer (X : Set G) := by
    rw [centralizer_eq_comap_of_disjoint_kernel f X hd]
    change f a ∈ centralizer (X.map f : Set Q)
    exact ha.symm ▸ hr
  have hp : a ^ m = 1 := by
    have h := hpow (e.symm ⟨a, hac⟩) (e.symm ⟨a, hac⟩).property
    have hh : (e.symm ⟨a, hac⟩) ^ m = 1 := Subtype.ext h
    have he := congrArg e hh
    simpa only [map_pow, map_one, e.apply_symm_apply, coe_pow, coe_one] using congrArg Subtype.val he
  apply ho
  apply orderOf_dvd_of_pow_eq_one
  simpa only [map_pow, map_one, ha] using congrArg f hp
end Subgroup

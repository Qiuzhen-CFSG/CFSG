module

public import Theory.GroupTheory.SolvableResidual

/-!
# Lifting a perfect subgroup through a solvable kernel

If C is normal in a perfect subgroup N and the image of N is contained in
that of C under a homomorphism with solvable kernel, then N = C. The kernel
inside N surjects onto N/C; this quotient is both solvable and perfect.
Normality is required only inside N, not in the ambient group.

This is the residual-action lifting step in Aschbacher--Smith,
*The Classification of Quasithin Groups*, E.1.11, printed p.213.
-/

open Subgroup

namespace Subgroup
variable {G Q : Type*} [Group G] [Group Q]

/-- A perfect subgroup lifts containment across a solvable kernel when the
comparison subgroup is normal in it. No ambient normality is assumed. -/
public theorem le_of_map_le_of_perfect_solvable_kernel
    (f : G →* Q) (N C : Subgroup G) [Group.IsPerfect N] [Group.IsSolvable f.ker]
    (hCN : C ≤ N) (hn : N ≤ normalizer (C : Set G))
    (hm : N.map f ≤ C.map f) : N ≤ C := by
  let D := C.subgroupOf N
  let : D.Normal := normal_subgroupOf_of_le_normalizer hn
  let R := f.ker.subgroupOf N
  let j : R →* f.ker :=
    { toFun := fun r => ⟨r.val.val, r.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => (z : G)) he
  let : Group.IsSolvable R := Group.isSolvable_of_isSolvable_injective hj
  let g := (QuotientGroup.mk' D).comp R.subtype
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D z
    obtain ⟨c, hc, he⟩ := hm (mem_map_of_mem f x.property)
    let cN : N := ⟨c, hCN hc⟩
    have hcD : cN ∈ D := hc
    have hk : cN⁻¹ * x ∈ R := by
      change f (c⁻¹ * (x : G)) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    refine ⟨⟨cN⁻¹ * x, hk⟩, ?_⟩
    change (QuotientGroup.mk' D) (cN⁻¹ * x) = _
    have hcq : (QuotientGroup.mk' D) cN = 1 := (QuotientGroup.eq_one_iff cN).mpr hcD
    rw [map_mul, map_inv, hcq, inv_one, one_mul]
  let : Group.IsSolvable (N ⧸ D) := Group.isSolvable_of_surjective hg
  have ht : D = ⊤ := top_unique (by simpa using solvableResidual_le_of_solvable_quotient D)
  exact subgroupOf_eq_top.mp ht
end Subgroup


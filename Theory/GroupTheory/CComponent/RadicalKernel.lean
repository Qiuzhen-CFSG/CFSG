module

public import Theory.GroupTheory.CComponent.Radical

/-!
# Kernels of nontrivial actions of an intrinsic C-component

A proper normal subgroup of a finite C-component is solvable. Applying
this to the action kernel places it inside the solvable radical. The
intrinsic top-subgroup formulation applies to a local component without
requiring it to be subnormal in the full ambient group.

Source: Aschbacher--Smith A.3.3(1), p.42, and the kernel argument in
13.1.4(5), p.867.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G D : Type*} [Group G] [Finite G] [Group D]

theorem kernel_le_solvableRadical_of_top_isCComponent (hG : (⊤ : Subgroup G).IsCComponent)
    (f : G →* D) (hne : f.ker ≠ ⊤) : f.ker ≤ solvableRadical G := by
  let N := f.ker.subgroupOf (⊤ : Subgroup G)
  have hN : N ≠ ⊤ := by
    intro he
    apply hne
    have hh := congrArg (Subgroup.map (⊤ : Subgroup G).subtype) he
    simpa only [N, map_subgroupOf_eq_of_le le_top, ← MonoidHom.range_eq_map,
      range_subtype] using hh
  let : Group.IsSolvable N := hG.isSolvable_of_subnormal_lt_top
    (inferInstance : N.Normal).isSubnormal hN
  let e : N ≃* f.ker := subgroupOfEquivOfLe le_top
  let : Group.IsSolvable f.ker := Group.isSolvable_of_surjective
    (f := e.toMonoidHom) e.surjective
  exact le_solvableRadical f.ker inferInstance inferInstance

end Theory.GroupTheory

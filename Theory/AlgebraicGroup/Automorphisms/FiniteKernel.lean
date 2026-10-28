module

public import Theory.AlgebraicGroup.Dimension.Fiber

/-!
# Finite-kernel endomorphisms of connected algebraic groups

This module records the dimension argument used in Steinberg's solvable Lang
induction.  If an algebraic-group endomorphism of a connected group has finite
kernel, the kernel-image dimension formula shows that its image has the same
dimension as the group.  A closed subgroup of equal dimension contains the
identity component, and connectedness makes that component the whole group.

This is the small geometric input needed for the abelian terminal step in
Steinberg, Theorem 10.4, and for restrictions of Steinberg endomorphisms to
connected closed subgroups.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A finite-kernel endomorphism of a connected algebraic group is
point-surjective. -/
public theorem connected_endomorphism_surjective_of_finiteKernel
    {G : Variety k} [AlgebraicGroup G]
    (f : AlgebraicGroup.Morphism G G)
    (hG : Variety.IsConnected G)
    (hker : Finite f.kernel) :
    Function.Surjective f.onPoints := by
  let K := f.kernelClosedSubgroup
  have hKsubfinite : Finite K.toSubgroup := by
    let e : K.toSubgroup ≃ f.kernel :=
      Equiv.setCongr (AlgebraicGroup.Morphism.kernelClosedSubgroup_carrier f)
    exact (Equiv.finite_iff e).2 hker
  let _ : Finite (Variety.Point K.carrierVariety) :=
    (Equiv.finite_iff K.pointEquiv).2 hKsubfinite
  have hKdim : Variety.dimension K.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points K.carrierVariety).2 inferInstance
  have hdim : Variety.dimension f.imageClosedSubgroup.carrierVariety =
      Variety.dimension G := by
    have hdimension := morphism_dimension_eq_kernel_add_image f
    rw [show f.kernelClosedSubgroup = K from rfl, hKdim, zero_add] at hdimension
    exact hdimension.symm
  have hcontains :=
    (closedSubgroup_dimension_eq_iff_contains_identityComponent
      G f.imageClosedSubgroup).1 hdim
  have hGid : AlgebraicGroup.identityComponent G = Set.univ :=
    (identityComponent_eq_univ_iff_isConnected G).2 hG
  intro y
  have hy : y ∈ f.imageClosedSubgroup.toSubgroup := by
    apply hcontains
    rw [hGid]
    trivial
  change y ∈ f.image at hy
  exact hy

end Theory.AlgebraicGroup

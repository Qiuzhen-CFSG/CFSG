module

public import Theory.AlgebraicGroup.Unipotent.Basic
public import Mathlib.GroupTheory.PGroup

/-!
# Unipotent point groups in defining characteristic

An algebraic unipotent group in characteristic `p` has a p-group of points,
even when the field is infinite. Embed it in an upper-unitriangular group
and use the p-power exponent bound there. Consequently intersections with
finite fixed-point groups are p-subgroups.

Source: GLS3, §§1.2--1.3 and the proof of Theorem 2.3.4(c).
-/

namespace Theory.AlgebraicGroup

variable {k : Type*} [Field k] [IsAlgClosed k]
  {K : Variety k} [AlgebraicGroup K]

/-- Unipotent algebraic groups have p-groups of points in characteristic p. -/
public theorem IsUnipotentAlgebraicGroup.isPGroup
    (hK : IsUnipotentAlgebraicGroup K) (p : ℕ) [Fact p.Prime] [CharP k p] :
    IsPGroup p (Variety.Point K) := by
  obtain ⟨n, H, ⟨e⟩⟩ := upperUnitriangularIso_of_unipotent hK
  let := H.carrierAlgebraicGroup
  let f := H.inclusion.onPoints.comp e.hom.onPoints
  have hf : Function.Injective f := by
    intro x y h
    have hxy : e.hom.onPoints x = e.hom.onPoints y := by
      apply H.pointEquiv.injective
      exact Subtype.ext h
    simpa only [e.hom_inv_id] using congrArg e.inv.onPoints hxy
  exact (show IsPGroup p (Variety.Point (uVariety k n)) from
    fun x => ⟨n, uPoint_pow_primePower_eq_one p n x⟩).of_injective f hf

/-- The embedded point subgroup of a closed unipotent group is a p-group. -/
public theorem ClosedSubgroup.isPGroup_of_unipotent
    (U : ClosedSubgroup K) (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (p : ℕ) [Fact p.Prime] [CharP k p] : IsPGroup p U.toSubgroup := by
  let f : U.toSubgroup →* Variety.Point U.carrierVariety :=
    { toFun := U.pointEquiv.symm
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact (hU.isPGroup p).of_injective f U.pointEquiv.symm.injective

end Theory.AlgebraicGroup

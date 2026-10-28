module

public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Dimension.Finite

universe u

/-! Finiteness criteria for kernels of algebraic-group morphisms. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A zero-dimensional kernel closed subgroup has finite point kernel. -/
public lemma Morphism.kernel_finite_of_kernelClosedSubgroup_dimension_eq_zero
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hkernel : Variety.dimension f.kernelClosedSubgroup.carrierVariety = 0) :
    Finite f.kernel := by
  have : Finite (Variety.Point f.kernelClosedSubgroup.carrierVariety) :=
    (dimension_zero_iff_finite_points f.kernelClosedSubgroup.carrierVariety).mp hkernel
  exact (f.kernelClosedSubgroup.pointEquiv.finite_iff).mp inferInstance

end Theory.AlgebraicGroup

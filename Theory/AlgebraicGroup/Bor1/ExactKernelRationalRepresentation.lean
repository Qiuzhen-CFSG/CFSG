module

public import Theory.AlgebraicGroup.Representations.Rational

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

/-- A finite-dimensional rational representation together with its exact
point-group kernel.  The carrier is hidden so constructions may choose a
convenient representation space without exposing a large dependent type. -/
public structure ExactKernelRationalRepresentation
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Variety k} [AlgebraicGroup G]
    (N : Subgroup (Variety.Point G)) where
  V : Type u
  [addCommGroup : AddCommGroup V]
  [module : Module k V]
  [finiteDimensional : FiniteDimensional k V]
  representation : RationalRepresentation G V
  isRational : IsRationalRepresentation representation
  pointKernel : representation.action.ker = N

end Theory.AlgebraicGroup.Bor1

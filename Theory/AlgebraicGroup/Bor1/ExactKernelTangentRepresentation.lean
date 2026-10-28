module

public import Theory.AlgebraicGroup.Bor1.ChevalleyWeightDifferentialKernel
public import Theory.AlgebraicGroup.Bor1.RepresentationDifferentialKernelEquivalence

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

set_option linter.style.haveILetI false in
/-- The exact kernel supplied by Bor1's representation construction is also
the kernel of the ordinary tangent morphism into the general linear group. -/
public theorem ExactKernelDifferentialRationalRepresentation.tangentKernel
    (H : ClosedSubgroup G)
    (P : ExactKernelDifferentialRationalRepresentation H) :
    LinearMap.ker (identityTangentMorphismLinearMap P.morphism) =
      LinearMap.range (identityTangentMorphismLinearMap H.inclusion) := by
  letI : AddCommGroup P.V := P.addCommGroup
  letI : Module k P.V := P.module
  letI : FiniteDimensional k P.V := P.finiteDimensional
  rw [← P.differentialKernel]
  ext D
  simp only [LinearMap.mem_ker]
  exact identityTangentMorphismLinearMap_eq_zero_iff_rationalRepresentationDifferential_eq_zero
    P.representation P.basis P.morphism D

end Theory.AlgebraicGroup.Bor1

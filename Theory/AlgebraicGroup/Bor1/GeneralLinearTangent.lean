module

public import Theory.AlgebraicGroup.Bor1.GeneralLinearTangentMatrixUnits

/-!
# The identity tangent space of the general-linear variety

Matrix-coordinate differentiation identifies the identity tangent space of
the general-linear variety with the full endomorphism space. Injectivity is
proved from the determinant relation in `GeneralLinearTangentCoordinates`;
surjectivity is proved by realizing matrix units in
`GeneralLinearTangentMatrixUnits`.
-/

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Matrix-coordinate differentiation identifies the identity tangent space of
the general-linear variety with all endomorphisms. -/
public theorem generalLinearIdentityTangentLinearMap_bijective
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Function.Bijective (generalLinearIdentityTangentLinearMap b) :=
  ⟨generalLinearIdentityTangentLinearMap_injective b,
    generalLinearIdentityTangentLinearMap_surjective b⟩

end Theory.AlgebraicGroup.Bor1


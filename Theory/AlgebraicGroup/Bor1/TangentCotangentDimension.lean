module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Theory.AlgebraicGroup.Bor1.PointDerivationCotangent

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The tangent space at the identity and the cotangent space at the identity
have the same finite dimension. -/
public theorem identityPointDerivation_finrank_eq_cotangent
    (K : Variety k) [AlgebraicGroup K] :
    Module.finrank k (IdentityPointDerivation K) =
      Module.finrank k (K.pointPrime 1).asIdeal.Cotangent := by
  let e := identityPointDerivationEquivCotangentDual K
  let _ : FiniteDimensional k
      ((K.pointPrime 1).asIdeal.Cotangent →ₗ[k] k) :=
    LinearEquiv.finiteDimensional e
  let _ : FiniteDimensional k (K.pointPrime 1).asIdeal.Cotangent :=
    (Module.finite_dual_iff k).mp inferInstance
  exact e.finrank_eq.trans Subspace.dual_finrank_eq

end Theory.AlgebraicGroup.Bor1

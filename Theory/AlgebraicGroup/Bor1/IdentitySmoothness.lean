module

public import Theory.AlgebraicGroup.Bor1.CoordinateRingSmooth
public import Theory.AlgebraicGroup.Bor1.IdentityCotangentDifferential
public import Theory.AlgebraicGroup.Bor1.SmoothAtOfCotangentInjective

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]

set_option linter.style.haveILetI false in
/-- A morphism of algebraic groups with surjective identity differential is
smooth at the identity point of its source. -/
public theorem identity_isSmoothAt_of_tangent_surjective
    (f : AlgebraicGroup.Morphism G Q)
    (hdf : Function.Surjective (identityTangentMorphismLinearMap f)) :
    letI : Algebra (Variety.PolynomialFunction Q)
        (Variety.PolynomialFunction G) :=
      f.toVariety.pullbackAlgHom.toRingHom.toAlgebra
    Algebra.IsSmoothAt (Variety.PolynomialFunction Q)
      (G.pointPrime 1).asIdeal := by
  let A := Variety.PolynomialFunction Q
  let B := Variety.PolynomialFunction G
  let F := f.toVariety.pullbackAlgHom
  letI : Algebra A B := F.toRingHom.toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun r =>
    (F.commutes r).symm
  letI : Algebra.Smooth k A := polynomialFunction_smooth_of_algebraicGroup Q
  letI : Algebra.Smooth k B := polynomialFunction_smooth_of_algebraicGroup G
  let eA : A →ₐ[k] k := polynomialFunctionPointAlgHom Q 1
  let eB : B →ₐ[k] k := polynomialFunctionPointAlgHom G 1
  letI : (RingHom.ker eB).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective eB
      (polynomialFunctionPointAlgHom_surjective G 1)
  have hcomm : eB.comp (IsScalarTower.toAlgHom k A B) = eA := by
    ext a
    change a (f.onPoints 1) = a 1
    exact congrArg a f.map_one
  have hcot : Function.Injective
      (Ideal.mapCotangent (RingHom.ker eA) (RingHom.ker eB)
        (IsScalarTower.toAlgHom k A B) (by
          intro x hx
          change (eB.comp (IsScalarTower.toAlgHom k A B)) x = 0
          rw [hcomm]
          exact hx)) := by
    change Function.Injective (identityCotangentMorphismLinearMap f)
    exact identityCotangentMorphismLinearMap_injective_of_tangent_surjective
      f hdf
  exact smoothAt_of_augmentedCotangentMap_injective eA eB
    (polynomialFunctionPointAlgHom_surjective Q 1)
    (polynomialFunctionPointAlgHom_surjective G 1) hcomm hcot

end Theory.AlgebraicGroup.Bor1

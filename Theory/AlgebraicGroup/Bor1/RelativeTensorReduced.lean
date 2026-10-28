module

public import Theory.AlgebraicGroup.Bor1.GlobalSmoothness
public import Theory.AlgebraicGroup.Bor1.SmoothReduced

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped TensorProduct

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]

set_option linter.style.haveILetI false in
/-- The relative self-product coordinate algebra of a group morphism with
surjective identity differential is reduced. -/
public theorem pullbackRelativeTensor_isReduced_of_tangent_surjective
    (f : AlgebraicGroup.Morphism G Q)
    (hdf : Function.Surjective (identityTangentMorphismLinearMap f)) :
    letI : Algebra (Variety.PolynomialFunction Q)
        (Variety.PolynomialFunction G) := f.toVariety.pullbackRingHom.toAlgebra
    IsReduced
      (Variety.PolynomialFunction G ⊗[Variety.PolynomialFunction Q]
        Variety.PolynomialFunction G) := by
  let C := Variety.PolynomialFunction Q
  let A := Variety.PolynomialFunction G
  let F := f.toVariety.pullbackRingHom
  letI : Algebra C A := F.toAlgebra
  let T := A ⊗[C] A
  change IsReduced T
  letI : Algebra.Smooth C A :=
    pullbackRingHom_smooth_of_tangent_surjective f hdf
  letI : Algebra.Smooth A T := inferInstance
  letI : Algebra.Smooth k A := polynomialFunction_smooth_of_algebraicGroup G
  letI : IsScalarTower k A T := inferInstance
  letI : Algebra.Smooth k T := Algebra.Smooth.comp k A T
  exact isReduced_of_smooth_of_field (K := k) (A := T)

end Theory.AlgebraicGroup.Bor1

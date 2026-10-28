module

public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
public import Theory.AlgebraicGroup.Bor1.FaithfullyFlatProjection
public import Theory.AlgebraicGroup.Bor1.InvariantTensorEquality

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped TensorProduct

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]

set_option linter.style.haveILetI false in
/-- A point-surjective algebraic-group morphism with surjective identity
differential pulls the coordinate ring of its target onto the right-invariant
coordinates of its kernel. -/
public theorem pullbackToRightInvariantCoordinateRing_surjective
    (H : ClosedSubgroup G) (f : AlgebraicGroup.Morphism G Q)
    (hsurj : Function.Surjective f.onPoints)
    (hker : f.kernel = H.toSubgroup)
    (hdf : Function.Surjective (identityTangentMorphismLinearMap f)) :
    Function.Surjective
      (f.pullbackToRightInvariantCoordinateRing H (by rw [hker])) := by
  let C := Variety.PolynomialFunction Q
  let A := Variety.PolynomialFunction G
  let F := f.toVariety.pullbackRingHom
  letI : Algebra C A := F.toAlgebra
  letI : Module.FaithfullyFlat C A := by
    exact pullbackRingHom_faithfullyFlat_of_surjective_of_tangent_surjective
      f hsurj hdf
  have heffective : Algebra.IsEffective C A :=
    Algebra.IsEffective.of_faithfullyFlat C A
  intro b
  have hbEqualizer : b.1 ∈
      Algebra.TensorProduct.includeLeftRingHom.eqLocus
        Algebra.TensorProduct.includeRight.toRingHom
        (S := A ⊗[C] A) := by
    change Algebra.TensorProduct.includeLeft
        (R := C) (S := k) b.1 =
      Algebra.TensorProduct.includeRight (R := C) b.1
    exact rightInvariant_includeLeft_eq_includeRight H f hker hdf b
  have hbRange : b.1 ∈ Set.range (algebraMap C A) :=
    (Set.ext_iff.mp
      (Algebra.IsEffective.eqLocus_includeLeft_includeRight heffective)
      b.1).mp hbEqualizer
  obtain ⟨q, hq⟩ := hbRange
  refine ⟨q, Subtype.ext ?_⟩
  change F q = b.1
  simpa [F, RingHom.algebraMap_toAlgebra] using hq

end Theory.AlgebraicGroup.Bor1

module

public import Theory.AlgebraicGroup.Bor1.MaximalAlgHom
public import Theory.AlgebraicGroup.Bor1.RelativeTensorReduced
public import Theory.AlgebraicGroup.ClosedSubgroup.InvariantCoordinates

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped TensorProduct

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]

set_option linter.style.haveILetI false in
/-- A right-invariant coordinate has equal left and right images in the
relative self-tensor product of a separable group projection with kernel H. -/
public theorem rightInvariant_includeLeft_eq_includeRight
    (H : ClosedSubgroup G) (f : AlgebraicGroup.Morphism G Q)
    (hker : f.kernel = H.toSubgroup)
    (hdf : Function.Surjective (identityTangentMorphismLinearMap f))
    (b : rightInvariantCoordinateRing H) :
    letI : Algebra (Variety.PolynomialFunction Q)
        (Variety.PolynomialFunction G) := f.toVariety.pullbackRingHom.toAlgebra
    Algebra.TensorProduct.includeLeft
        (R := Variety.PolynomialFunction Q) (S := k) b.1 =
      Algebra.TensorProduct.includeRight
        (R := Variety.PolynomialFunction Q) b.1 := by
  let C := Variety.PolynomialFunction Q
  let A := Variety.PolynomialFunction G
  let F := f.toVariety.pullbackRingHom
  letI : Algebra C A := F.toAlgebra
  letI : IsScalarTower k C A := IsScalarTower.of_algebraMap_eq' (by
    exact f.toVariety.pullbackAlgHom.comp_algebraMap.symm)
  let T := A ⊗[C] A
  change (Algebra.TensorProduct.includeLeft (R := C) (S := k) b.1 : T) =
    Algebra.TensorProduct.includeRight (R := C) b.1
  letI : Algebra.Smooth C A :=
    pullbackRingHom_smooth_of_tangent_surjective f hdf
  letI : Algebra.Smooth A T := inferInstance
  letI : Algebra.Smooth k A := polynomialFunction_smooth_of_algebraicGroup G
  letI : IsScalarTower k A T := inferInstance
  letI : Algebra.Smooth k T := Algebra.Smooth.comp k A T
  letI : Algebra.FiniteType k T := inferInstance
  letI : IsReduced T :=
    pullbackRelativeTensor_isReduced_of_tangent_surjective f hdf
  letI : IsJacobsonRing T :=
    isJacobsonRing_of_finiteType (A := k) (B := T)
  rw [← sub_eq_zero]
  apply IsReduced.eq_zero
  rw [← mem_nilradical]
  change (Algebra.TensorProduct.includeLeft (R := C) (S := k) b.1 : T) -
    Algebra.TensorProduct.includeRight (R := C) b.1 ∈
      Ideal.radical (⊥ : Ideal T)
  rw [Ideal.radical_eq_jacobson, Ideal.jacobson, Ideal.mem_sInf]
  intro m hm
  obtain ⟨-, hmmax⟩ := hm
  obtain ⟨φ, hφker⟩ :=
    exists_algHom_ker_eq_of_isMaximal_finiteType (k := k) m hmmax
  let iL : A →ₐ[k] T :=
    Algebra.TensorProduct.includeLeft (R := C) (S := k) (A := A) (B := A)
  let iR : A →ₐ[k] T :=
    (Algebra.TensorProduct.includeRight
      (R := C) (A := A) (B := A)).restrictScalars k
  let φL : A →ₐ[k] k := φ.comp iL
  let φR : A →ₐ[k] k := φ.comp iR
  let gL : Variety.Point G :=
    (polynomialFunctionPointAlgHomEquiv G).symm φL
  let gR : Variety.Point G :=
    (polynomialFunctionPointAlgHomEquiv G).symm φR
  have hgL : polynomialFunctionPointAlgHom G gL = φL :=
    (polynomialFunctionPointAlgHomEquiv G).apply_symm_apply φL
  have hgR : polynomialFunctionPointAlgHom G gR = φR :=
    (polynomialFunctionPointAlgHomEquiv G).apply_symm_apply φR
  have hfg : f.onPoints gL = f.onPoints gR := by
    apply (polynomialFunctionPointAlgHomEquiv Q).injective
    apply AlgHom.ext
    intro c
    calc
      polynomialFunctionPointAlgHom Q (f.onPoints gL) c =
          polynomialFunctionPointAlgHom G gL (F c) := by rfl
      _ = φ (iL (F c)) := by rw [hgL]; rfl
      _ = φ (iR (F c)) := by
        congr 1
        dsimp [iL, iR, F]
        exact DFunLike.congr_fun
          Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap c
      _ = polynomialFunctionPointAlgHom G gR (F c) := by rw [hgR]; rfl
      _ = polynomialFunctionPointAlgHom Q (f.onPoints gR) c := by rfl
  have hdiffKer : gL⁻¹ * gR ∈ f.kernel := by
    change f.onPoints (gL⁻¹ * gR) = 1
    rw [map_mul, f.map_inv, hfg]
    simp
  have hdiffH : gL⁻¹ * gR ∈ H.toSubgroup := by
    rw [← hker]
    exact hdiffKer
  have hbEq : b.1 gL = b.1 gR := by
    have hb := (mem_rightInvariantCoordinateRing_iff H b.1).mp b.property
      gL (gL⁻¹ * gR) hdiffH
    simpa [mul_assoc] using hb.symm
  rw [← hφker]
  change φ ((Algebra.TensorProduct.includeLeft (R := C) (S := k) b.1 : T) -
    Algebra.TensorProduct.includeRight (R := C) b.1) = 0
  rw [map_sub, sub_eq_zero]
  calc
    φ (Algebra.TensorProduct.includeLeft (R := C) (S := k) b.1 : T) =
        b.1 gL := by
      have h := AlgHom.congr_fun hgL b.1
      exact h.symm
    _ = b.1 gR := hbEq
    _ = φ (Algebra.TensorProduct.includeRight (R := C) b.1 : T) := by
      have h := AlgHom.congr_fun hgR b.1
      exact h

end Theory.AlgebraicGroup.Bor1

module

public import Mathlib.Algebra.Lie.OfAssociative
public import Theory.AlgebraicGroup.Bor1.GeneralLinearTangent
public import Theory.AlgebraicGroup.RootSubgroups.TangentLie

/-!
# The tangent Lie algebra of the general-linear variety

The matrix-coordinate equivalence for the identity tangent space of `GL(V)`
respects Lie brackets. Coordinate comultiplication is matrix multiplication,
so convolution of tangent derivations becomes composition of endomorphisms and
the canonical tangent bracket becomes the commutator. This gives the target
used for differentials of rational representations.
-/

open scoped BigOperators
open WithConv

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Linear endomorphisms carry their commutator Lie ring structure. -/
public instance generalLinearEndomorphismLieRing : LieRing (Module.End k V) :=
  LieRing.ofAssociativeRing

private lemma generalLinearMatrixCoordinate_comultiplication
    (n : Nat) (i j : Fin n) :
    coordinateComultiplication (glVariety n : Variety k)
        (generalLinearMatrixCoordinate n i j) =
      ∑ c, generalLinearMatrixCoordinate n i c ⊗ₜ[k]
        generalLinearMatrixCoordinate n c j := by
  apply polynomialFunctionTensor_injective
    (glVariety n : Variety k) (glVariety n : Variety k)
  apply Variety.PolynomialFunction.ext
  intro z
  let xy := Variety.prodPointEquiv
    (glVariety n : Variety k) (glVariety n : Variety k) z
  rcases hxy : xy with ⟨x, y⟩
  have hz : z =
      (Variety.prodPointEquiv
        (glVariety n : Variety k) (glVariety n : Variety k)).symm (x, y) := by
    apply (Variety.prodPointEquiv
      (glVariety n : Variety k) (glVariety n : Variety k)).injective
    rw [Equiv.apply_symm_apply]
    exact hxy
  rw [hz, coordinateComultiplication_apply]
  rw [map_sum]
  simp only [polynomialFunctionTensor_tmul]
  change generalLinearMatrixCoordinate n i j (x * y) =
    polynomialFunctionEvalAddHom
      (Variety.prod (glVariety n : Variety k) (glVariety n : Variety k))
      ((Variety.prodPointEquiv
        (glVariety n : Variety k) (glVariety n : Variety k)).symm (x, y))
      (∑ c, polynomialFunctionLeft
          (glVariety n : Variety k) (glVariety n : Variety k)
            (generalLinearMatrixCoordinate n i c) *
        polynomialFunctionRight
          (glVariety n : Variety k) (glVariety n : Variety k)
            (generalLinearMatrixCoordinate n c j))
  rw [map_sum]
  simp only [polynomialFunctionEvalAddHom_apply,
    polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
    polynomialFunctionRight_apply, Equiv.apply_symm_apply]
  simp_rw [generalLinearMatrixCoordinate_apply]
  let e := translationGLPointMulEquiv (k := k) n
  change ((e (x * y) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
    ∑ c, ((e x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i c *
      ((e y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c j
  rw [map_mul]
  exact Matrix.mul_apply

private lemma generalLinearIdentityTangentConvolution_matrixCoordinate
    (D E : IdentityPointDerivation (glVarietyOf k V))
    (i j : Fin (Module.finrank k V)) :
    identityTangentConvolution (glVarietyOf k V) D E
        (generalLinearMatrixCoordinateOf V i j) =
      ∑ c, D (generalLinearMatrixCoordinateOf V i c) *
        E (generalLinearMatrixCoordinateOf V c j) := by
  let _ : Bialgebra k
      (Variety.PolynomialFunction (glVarietyOf k V)) :=
    coordinateBialgebra (glVarietyOf k V)
  let r : Coalgebra.Repr k
      (generalLinearMatrixCoordinateOf V i j)
      (Fin (Module.finrank k V)) :=
    { index := Finset.univ
      left := fun c => generalLinearMatrixCoordinateOf V i c
      right := fun c => generalLinearMatrixCoordinateOf V c j
      eq := by
        change (∑ c, generalLinearMatrixCoordinate
            (Module.finrank k V) i c ⊗ₜ[k]
              generalLinearMatrixCoordinate (Module.finrank k V) c j) =
          coordinateComultiplication
            (glVariety (Module.finrank k V) : Variety k)
              (generalLinearMatrixCoordinate (Module.finrank k V) i j)
        exact (generalLinearMatrixCoordinate_comultiplication
          (k := k) (Module.finrank k V) i j).symm }
  change (toConv D.toLinearMap * toConv E.toLinearMap).ofConv
      (generalLinearMatrixCoordinateOf V i j) = _
  rw [r.convMul_apply]
  change (∑ c ∈ Finset.univ,
    D (generalLinearMatrixCoordinateOf V i c) *
      E (generalLinearMatrixCoordinateOf V c j)) = _
  simp

private lemma basis_coord_end_mul
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (A B : Module.End k V) (i j : Fin (Module.finrank k V)) :
    b.coord i ((A * B) (b j)) =
      ∑ c, b.coord i (A (b c)) * b.coord c (B (b j)) := by
  classical
  change b.coord i (A (B (b j))) = _
  conv_lhs => rw [← b.sum_repr (B (b j))]
  rw [map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro c _
  exact mul_comm _ _

/-- Matrix-coordinate differentiation sends the canonical tangent bracket to the endomorphism commutator. -/
public theorem generalLinearIdentityTangentLinearMap_map_bracket
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (D E : IdentityPointDerivation (glVarietyOf k V)) :
    generalLinearIdentityTangentLinearMap b ⁅D, E⁆ =
      ⁅generalLinearIdentityTangentLinearMap b D,
        generalLinearIdentityTangentLinearMap b E⁆ := by
  apply LinearMap.ext_on b.span_eq
  rintro _ ⟨j, rfl⟩
  apply b.ext_elem
  intro i
  change b.coord i
      (generalLinearIdentityTangentLinearMap b ⁅D, E⁆ (b j)) =
    b.coord i
      (⁅generalLinearIdentityTangentLinearMap b D,
        generalLinearIdentityTangentLinearMap b E⁆ (b j))
  rw [generalLinearIdentityTangentLinearMap_apply_basis_coord]
  change identityTangentBracket (glVarietyOf k V) D E
      (generalLinearMatrixCoordinateOf V i j) = _
  rw [identityTangentBracket_apply,
    generalLinearIdentityTangentConvolution_matrixCoordinate,
    generalLinearIdentityTangentConvolution_matrixCoordinate,
    Ring.lie_def, LinearMap.sub_apply, map_sub,
    basis_coord_end_mul, basis_coord_end_mul]
  simp_rw [generalLinearIdentityTangentLinearMap_apply_basis_coord]

/-- Matrix-coordinate differentiation as a Lie algebra homomorphism. -/
@[expose]
public noncomputable def generalLinearIdentityTangentLieHom
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    IdentityPointDerivation (glVarietyOf k V) →ₗ⁅k⁆ Module.End k V where
  __ := generalLinearIdentityTangentLinearMap b
  map_lie' := by
    intro D E
    exact generalLinearIdentityTangentLinearMap_map_bracket b D E

/-- The basis-dependent Lie equivalence from the identity tangent space of the
general-linear variety to the endomorphism Lie algebra. -/
@[expose]
public noncomputable def generalLinearIdentityTangentLieEquiv
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    IdentityPointDerivation (glVarietyOf k V) ≃ₗ⁅k⁆ Module.End k V :=
  LieEquiv.ofBijective (generalLinearIdentityTangentLieHom b) (by
    change Function.Bijective (generalLinearIdentityTangentLinearMap b)
    exact generalLinearIdentityTangentLinearMap_bijective b)

end Theory.AlgebraicGroup.Bor1

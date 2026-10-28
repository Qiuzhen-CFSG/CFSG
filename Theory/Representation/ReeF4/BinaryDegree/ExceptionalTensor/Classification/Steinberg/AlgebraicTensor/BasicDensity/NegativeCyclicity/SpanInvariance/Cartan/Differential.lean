module

public import Mathlib.Algebra.Lie.OfAssociative
public import Theory.AlgebraicGroup.Bor1.GeneralLinearTangentCoordinates
public import Theory.AlgebraicGroup.RootSubgroups.TangentLie

/-!
# Characteristic-independent transfer of tangent brackets

The matrix-coordinate equivalence for the identity tangent space of `GL(V)`
respects Lie brackets. Coordinate comultiplication is matrix multiplication,
so convolution of tangent derivations becomes composition of endomorphisms and
the canonical tangent bracket becomes the commutator. This gives the target
used for differentials of rational representations in characteristic two.

This is the bracket calculation from `Bor1.GeneralLinearTangentLie`, with
only its coordinate imports: its tangent equivalence and characteristic-zero
dimension arguments are unnecessary here. Source: Steinberg (1963), §§2, 4.
-/

open scoped BigOperators
open WithConv

universe u v

namespace Theory.AlgebraicGroup.Bor1
namespace ReeF4CartanDifferential

open Theory.AlgebraicGroup

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]


attribute [local instance] LieRing.ofAssociativeRing

/-- A coordinate of the tangent endomorphism is the derivative of the
corresponding general-linear matrix coordinate. -/
public theorem generalLinearIdentityTangentLinearMap_apply_basis_coord
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (D : IdentityPointDerivation (glVarietyOf k V))
    (i j : Fin (Module.finrank k V)) :
    b.coord i (generalLinearIdentityTangentLinearMap b D (b j)) =
      D (generalLinearMatrixCoordinateOf V i j) := by
  classical
  change b.repr
    ((∑ p, ∑ q,
      D (generalLinearMatrixCoordinateOf V p q) •
        b.end (p, q)) (b j)) i = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  simp_rw [b.end_apply_apply]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  change b.coord i
    (∑ p, D (generalLinearMatrixCoordinateOf V p j) • b p) = _
  rw [map_sum]
  simp only [map_smul, Module.Basis.coord_apply,
    Module.Basis.repr_self]
  rw [Finset.sum_eq_single i]
  · simp
  · intro c _ hci
    rw [Finsupp.single_eq_of_ne (Ne.symm hci), smul_zero]
  · simp

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


/-- Matrix-coordinate differentiation is injective on the identity tangent
space of the general-linear variety. -/
public theorem generalLinearIdentityTangentLinearMap_injective
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Function.Injective (generalLinearIdentityTangentLinearMap b) := by
  classical
  intro D E hDE
  let M : Matrix (Fin (Module.finrank k V))
      (Fin (Module.finrank k V))
      (Variety.PolynomialFunction (glVarietyOf k V)) :=
    fun i j => generalLinearMatrixCoordinateOf V i j
  let t : Variety.PolynomialFunction (glVarietyOf k V) :=
    Variety.PolynomialFunction.ofPolynomial (glVarietyOf k V)
      (MvPolynomial.X (Sum.inr PUnit.unit))
  have hmatrix (i j : Fin (Module.finrank k V)) :
      D (M i j) = E (M i j) := by
    have h := congrArg (fun A : Module.End k V => b.coord i (A (b j))) hDE
    change b.coord i (generalLinearIdentityTangentLinearMap b D (b j)) =
      b.coord i (generalLinearIdentityTangentLinearMap b E (b j)) at h
    rw [generalLinearIdentityTangentLinearMap_apply_basis_coord,
      generalLinearIdentityTangentLinearMap_apply_basis_coord] at h
    exact h
  have hMone (i j : Fin (Module.finrank k V)) :
      M i j 1 = if i = j then 1 else 0 := by
    change generalLinearMatrixCoordinate (Module.finrank k V) i j 1 = _
    rw [generalLinearMatrixCoordinate_apply]
    change (glMatrixOfPoint (Module.finrank k V)
      (1 : Variety.Point (glVarietyOf k V))) i j = _
    rw [show glMatrixOfPoint (Module.finrank k V)
        (1 : Variety.Point (glVarietyOf k V)) = 1 by rfl]
    exact Matrix.one_apply
  have hdet : D M.det = E M.det := by
    rw [identityPointDerivation_det_at_identity D M hMone,
      identityPointDerivation_det_at_identity E M hMone]
    exact Finset.sum_congr rfl fun i _ => hmatrix i i
  have hrelation : M.det * t = 1 := by
    apply Variety.PolynomialFunction.ext
    intro x
    change M.det x * t x = 1
    have hMx : M.det x = (glMatrixOfPoint (Module.finrank k V) x).det := by
      let ev := polynomialFunctionPointAlgHom (glVarietyOf k V) x
      change ev M.det = _
      rw [AlgHom.map_det]
      congr 1
      ext i j
      exact generalLinearMatrixCoordinate_apply _ _ _ x
    have htx : t x = glScalarOfPoint (Module.finrank k V) x := by
      change evalPolynomial x.val (MvPolynomial.X (Sum.inr PUnit.unit)) = _
      exact MvPolynomial.eval_X _
    rw [hMx, htx]
    exact glPoint_det_mul_scalar (Module.finrank k V) x
  have hD := congrArg D hrelation
  have hE := congrArg E hrelation
  rw [D.leibniz, D.map_one_eq_zero] at hD
  rw [E.leibniz, E.map_one_eq_zero] at hE
  have hMdet : M.det 1 = 1 := by
    have hMeval : (fun i j => M i j 1) =
        (1 : Matrix (Fin (Module.finrank k V))
          (Fin (Module.finrank k V)) k) := by
      ext i j
      exact hMone i j
    let ev := polynomialFunctionPointAlgHom (glVarietyOf k V) 1
    change ev M.det = 1
    rw [AlgHom.map_det]
    change Matrix.det (fun i j => M i j 1) = 1
    rw [hMeval, Matrix.det_one]
  have ht : D t = E t := by
    change M.det 1 * D t + t 1 * D M.det = 0 at hD
    change M.det 1 * E t + t 1 * E M.det = 0 at hE
    rw [hMdet] at hD hE
    simp only [one_mul] at hD hE
    have htail : t 1 * D M.det = t 1 * E M.det :=
      congrArg (t 1 * ·) hdet
    calc
      D t = -(t 1 * D M.det) := eq_neg_of_add_eq_zero_left hD
      _ = -(t 1 * E M.det) := congrArg Neg.neg htail
      _ = E t := (eq_neg_of_add_eq_zero_left hE).symm
  apply coordinateTangentMap_injective (glVarietyOf k V)
  funext c
  cases c with
  | inl ij =>
      rcases ij with ⟨i, j⟩
      change D (M i j) = E (M i j)
      exact hmatrix i j
  | inr q =>
      obtain rfl := Subsingleton.elim q PUnit.unit
      change D t = E t
      exact ht


end ReeF4CartanDifferential
end Theory.AlgebraicGroup.Bor1

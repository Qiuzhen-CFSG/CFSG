module

public import Theory.AlgebraicGroup.RootSubgroups.Tangent
public import Theory.AlgebraicGroup.Bor1.DerivationDeterminant
public import Theory.AlgebraicGroup.Representations.DiagonalBasis

/-!
# Matrix coordinates on the general-linear identity tangent

Differentiating the matrix-coordinate functions of the general-linear variety
assembles an identity tangent into an endomorphism in a chosen basis. The map
is injective: equality of all matrix-coordinate derivatives also forces
equality on the inverse-determinant coordinate through the defining
determinant relation.

This is the coordinate half of the general-linear tangent identification.
-/

open scoped BigOperators

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Scalar multiplication by the base field commutes with the residue-field
action of a polynomial function at the identity point. This aligns the legacy
Bor1 tangent module with the root-level tangent Lie API. -/
public instance identityPointSMulCommClass
    (K : Variety k) [AlgebraicGroup K] :
    SMulCommClass k (Variety.PolynomialFunction K) k where
  smul_comm c f x := by
    change c * (f 1 * x) = f 1 * (c * x)
    ring

/-- The `(i, j)` matrix-coordinate function on the basis-free general-linear variety. -/
@[expose]
public noncomputable def generalLinearMatrixCoordinateOf
    (V : Type v) [AddCommGroup V] [Module k V]
    (i j : Fin (Module.finrank k V)) :
    Variety.PolynomialFunction (glVarietyOf k V) := by
  change Variety.PolynomialFunction
    (glVariety (Module.finrank k V) : Variety k)
  exact generalLinearMatrixCoordinate (Module.finrank k V) i j

/-- Differentiate all matrix coordinates at the identity and assemble them as an
endomorphism in the chosen basis. -/
@[expose]
public noncomputable def generalLinearIdentityTangentLinearMap
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    IdentityPointDerivation (glVarietyOf k V) →ₗ[k] Module.End k V where
  toFun D := ∑ i, ∑ j,
    D (generalLinearMatrixCoordinateOf V i j) • b.end (i, j)
  map_add' := by
    intro D E
    ext x
    simp only [Derivation.add_apply, add_smul, Finset.sum_add_distrib,
      LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  map_smul' := by
    intro c D
    ext x
    simp only [Derivation.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum, LinearMap.smul_apply, LinearMap.sum_apply,
      RingHom.id_apply]

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

/-- Evaluating a general-linear matrix coordinate gives the corresponding
chosen-basis coefficient of the represented automorphism. -/
public theorem generalLinearMatrixCoordinateOf_eq_basis_coord
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : Variety.Point (glVarietyOf k V))
    (i j : Fin (Module.finrank k V)) :
    generalLinearMatrixCoordinateOf V i j x =
      b.coord i (((glPointEquivOf k V b x :
        LinearMap.GeneralLinearGroup k V) : Module.End k V) (b j)) := by
  change generalLinearMatrixCoordinate (Module.finrank k V) i j x = _
  rw [generalLinearMatrixCoordinate_apply]
  change glMatrixOfPoint (Module.finrank k V) x i j = _
  have hb := glPointEquivOf_apply_basis V b x j
  have hc := congrArg (b.coord i) hb
  rw [Module.Basis.coord_equivFun_symm] at hc
  exact hc.symm


end Theory.AlgebraicGroup.Bor1


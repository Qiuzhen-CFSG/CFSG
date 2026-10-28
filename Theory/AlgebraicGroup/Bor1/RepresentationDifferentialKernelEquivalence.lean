module

public import Theory.AlgebraicGroup.Bor1.DerivationDeterminant
public import Theory.AlgebraicGroup.Bor1.RepresentationDifferentialKernel
public import Theory.AlgebraicGroup.Bor1.RepresentationDifferentialMinor

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped BigOperators

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- The coordinate representation differential vanishes exactly when the
ordinary tangent morphism into the representing general linear group
vanishes. -/
public theorem identityTangentMorphismLinearMap_eq_zero_iff_rationalRepresentationDifferential_eq_zero
    (rho : RationalRepresentation G V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (D : IdentityPointDerivation G) :
    identityTangentMorphismLinearMap f D = 0 <->
      rationalRepresentationDifferential rho b f D = 0 := by
  classical
  constructor
  · exact rationalRepresentationDifferential_eq_zero_of_identityTangentMorphismLinearMap_eq_zero
      rho b f D
  · intro hzero
    let dF := identityTangentMorphismLinearMap f D
    let M : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V))
        (Variety.PolynomialFunction (glVarietyOf k V)) :=
      fun i j => generalLinearMatrixCoordinate (Module.finrank k V) i j
    let t : Variety.PolynomialFunction (glVarietyOf k V) :=
      Variety.PolynomialFunction.ofPolynomial
        (glVarietyOf k V)
        (MvPolynomial.X (Sum.inr PUnit.unit))
    have hmatrix (i j : Fin (Module.finrank k V)) :
        dF (generalLinearMatrixCoordinate (Module.finrank k V) i j) = 0 := by
      have hcoord : b.coord i
          (rationalRepresentationDifferential rho b f D (b j)) =
            D (rationalRepresentationMatrixCoefficient rho b f i j) := by
        rw [rationalRepresentationDifferential_linearMatrixCoefficient]
        rw [rationalRepresentationLinearMatrixCoefficient_basis]
      rw [hzero] at hcoord
      change D (rationalRepresentationMatrixCoefficient rho b f i j) = 0
      simpa using hcoord.symm
    have hMone (i j : Fin (Module.finrank k V)) :
        M i j 1 = if i = j then 1 else 0 := by
      change generalLinearMatrixCoordinate (Module.finrank k V) i j 1 = _
      rw [generalLinearMatrixCoordinate_apply]
      change (glMatrixOfPoint (Module.finrank k V)
        (1 : Variety.Point (glVarietyOf k V))) i j = _
      rw [show glMatrixOfPoint (Module.finrank k V)
          (1 : Variety.Point (glVarietyOf k V)) = 1 by
        rfl]
      exact Matrix.one_apply
    have hdet : dF M.det = 0 := by
      rw [identityPointDerivation_det_at_identity dF M hMone]
      simp [M, hmatrix]
    have hrelation : M.det * t = 1 := by
      apply Variety.PolynomialFunction.ext
      intro x
      change M.det x * t x = 1
      have hMx : M.det x =
          (glMatrixOfPoint (Module.finrank k V) x).det := by
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
    have ht : dF t = 0 := by
      have h := congrArg dF hrelation
      rw [dF.leibniz, dF.map_one_eq_zero, hdet] at h
      change M.det 1 * dF t + t 1 * 0 = 0 at h
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
      simpa [hMdet] using h
    apply Derivation.ext_of_adjoin_eq_top
      (Set.range fun c : (glVarietyOf k V).Coordinates =>
        Variety.PolynomialFunction.ofPolynomial
          (glVarietyOf k V) (MvPolynomial.X c))
    · rw [Algebra.adjoin_range_eq_range_aeval]
      apply (AlgHom.range_eq_top _).2
      intro q
      obtain ⟨p, hp⟩ := q.representedBy
      refine ⟨p, ?_⟩
      apply Variety.PolynomialFunction.ext
      intro x
      rw [hp]
      have haeval :
          MvPolynomial.aeval (fun c : (glVarietyOf k V).Coordinates =>
            Variety.PolynomialFunction.ofPolynomial
              (glVarietyOf k V) (MvPolynomial.X c)) =
            evaluationAlgHom (glVarietyOf k V) := by
        apply MvPolynomial.algHom_ext
        intro c
        apply Variety.PolynomialFunction.ext
        intro y
        rw [MvPolynomial.aeval_X]
        rfl
      rw [haeval]
      rfl
    · rintro _ ⟨c, rfl⟩
      cases c with
      | inl ij =>
          rcases ij with ⟨i, j⟩
          change dF (generalLinearMatrixCoordinate
            (Module.finrank k V) i j) = 0
          exact hmatrix i j
      | inr q =>
          obtain rfl := Subsingleton.elim q PUnit.unit
          change dF t = 0
          exact ht

end Theory.AlgebraicGroup.Bor1

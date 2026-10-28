module

public import Theory.AlgebraicGroup.Bor1.ConjugationRational
public import Theory.AlgebraicGroup.Bor1.RepresentationDifferentialMinor

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped BigOperators

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- At the identity, differentiating an inverse matrix coefficient negates
the corresponding original matrix-coefficient derivative. -/
public theorem rationalRepresentationInverseMatrixCoefficient_derivation
    (ρ : RationalRepresentation G V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V b (f.onPoints g) = ρ.action g)
    (D : IdentityPointDerivation G)
    (i j : Fin (Module.finrank k V)) :
    D (rationalRepresentationInverseMatrixCoefficient ρ b f i j) =
      -D (rationalRepresentationMatrixCoefficient ρ b f i j) := by
  have hinverse :
      (∑ r, rationalRepresentationMatrixCoefficient ρ b f i r *
          rationalRepresentationInverseMatrixCoefficient ρ b f r j) =
        algebraMap k G.PolynomialFunction (if i = j then 1 else 0) := by
    apply Variety.PolynomialFunction.ext
    intro g
    let ev : G.PolynomialFunction →+* k :=
      { toFun := fun q => q g
        map_one' := by
          rw [← (algebraMap k G.PolynomialFunction).map_one]
          exact polynomialFunction_algebraMap_apply G 1 g
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change ev (∑ r, rationalRepresentationMatrixCoefficient ρ b f i r *
      rationalRepresentationInverseMatrixCoefficient ρ b f r j) =
        ev (algebraMap k G.PolynomialFunction (if i = j then 1 else 0))
    rw [map_sum]
    simp_rw [map_mul]
    change (∑ r,
      rationalRepresentationMatrixCoefficient ρ b f i r g *
        rationalRepresentationInverseMatrixCoefficient ρ b f r j g) = _
    simp_rw [rationalRepresentationMatrixCoefficient_apply ρ b f hf]
    simp_rw [rationalRepresentationInverseMatrixCoefficient_apply ρ b f hf]
    change _ = (algebraMap k G.PolynomialFunction
      (if i = j then 1 else 0)) g
    rw [polynomialFunction_algebraMap_apply]
    simp_rw [← LinearMap.toMatrix_apply]
    rw [← Matrix.mul_apply]
    rw [← LinearMap.toMatrix_mul]
    have hone :
        ((ρ.action g : LinearMap.GeneralLinearGroup k V) : Module.End k V) *
            (((ρ.action g)⁻¹ : LinearMap.GeneralLinearGroup k V) :
              Module.End k V) = 1 := by
      calc
        _ = ((ρ.action g * (ρ.action g)⁻¹ :
            LinearMap.GeneralLinearGroup k V) : Module.End k V) :=
          (Units.val_mul (ρ.action g) (ρ.action g)⁻¹).symm
        _ = 1 := by rw [mul_inv_cancel]; rfl
    rw [hone, LinearMap.toMatrix_one, Matrix.one_apply]
  have hD := congrArg D hinverse
  simp only [map_sum] at hD
  simp_rw [D.leibniz] at hD
  rw [D.map_algebraMap] at hD
  simp only [Finset.sum_add_distrib, add_eq_zero_iff_eq_neg] at hD
  have hmatrix_one (a c : Fin (Module.finrank k V)) :
      rationalRepresentationMatrixCoefficient ρ b f a c 1 =
        if a = c then 1 else 0 := by
    rw [rationalRepresentationMatrixCoefficient_apply ρ b f hf, map_one]
    change b.repr (b c) a = _
    simpa [eq_comm] using Module.Basis.repr_self_apply b c a
  have hinverse_one (a c : Fin (Module.finrank k V)) :
      rationalRepresentationInverseMatrixCoefficient ρ b f a c 1 =
        if a = c then 1 else 0 := by
    rw [rationalRepresentationInverseMatrixCoefficient_apply ρ b f hf, map_one]
    change b.repr (b c) a = _
    simpa [eq_comm] using Module.Basis.repr_self_apply b c a
  have hsmul (q : G.PolynomialFunction) (a : k) : q • a = q 1 * a := rfl
  simp_rw [hsmul, hmatrix_one, hinverse_one] at hD
  simpa [Finset.sum_ite_irrel, Finset.sum_ite_eq', eq_comm] using hD

/-- The adjoint endomorphism `u ↦ A * u - u * A`. -/
@[expose]
public def endomorphismCommutator (A : Module.End k V) :
    Module.End k (Module.End k V) where
  toFun u := A * u - u * A
  map_add' u v := by
    ext x
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      map_add]
    abel
  map_smul' c u := by
    ext x
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      map_smul, RingHom.id_apply]
    rw [smul_sub]

/-- The differential of conjugation by a rational representation is the
commutator with the original representation differential. -/
public theorem rationalRepresentationDifferential_conjEnd_apply
    (ρ : RationalRepresentation G V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V b (f.onPoints g) = ρ.action g)
    (e : Module.Basis (Fin (Module.finrank k (Module.End k V))) k
      (Module.End k V))
    (q : AlgebraicGroup.Morphism G (glVarietyOf k (Module.End k V)))
    (hq : ∀ g, glPointEquivOf k (Module.End k V) e (q.onPoints g) =
      (conjEndRationalRepresentation ρ).action g)
    (D : IdentityPointDerivation G) :
    rationalRepresentationDifferential (conjEndRationalRepresentation ρ) e q D =
      endomorphismCommutator (rationalRepresentationDifferential ρ b f D) := by
  let A := rationalRepresentationDifferential ρ b f D
  have hA (r s : Fin (Module.finrank k V)) :
      b.coord r (A (b s)) =
        D (rationalRepresentationMatrixCoefficient ρ b f r s) := by
    change b.coord r
      (rationalRepresentationDifferential ρ b f D (b s)) = _
    rw [rationalRepresentationDifferential_linearMatrixCoefficient]
    rw [rationalRepresentationLinearMatrixCoefficient_basis]
  apply LinearMap.ext
  intro u
  rw [← b.end.sum_repr u]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro ac hac
  congr 1
  apply b.end.ext_elem
  intro pq
  rcases ac with ⟨a, c⟩
  rcases pq with ⟨p, qidx⟩
  change b.end.coord (p, qidx)
      (rationalRepresentationDifferential
        (conjEndRationalRepresentation ρ) e q D
          (b.end (a, c))) =
    b.end.coord (p, qidx)
      (endomorphismCommutator A (b.end (a, c)))
  rw [rationalRepresentationDifferential_linearMatrixCoefficient]
  have hcoefficient :
      rationalRepresentationLinearMatrixCoefficient
          (conjEndRationalRepresentation ρ) e q
          (b.end.coord (p, qidx)) (b.end (a, c)) =
        rationalRepresentationMatrixCoefficient ρ b f p a *
          rationalRepresentationInverseMatrixCoefficient ρ b f c qidx := by
    apply Variety.PolynomialFunction.ext
    intro g
    rw [rationalRepresentationLinearMatrixCoefficient_apply
      (conjEndRationalRepresentation ρ) e q hq]
    change b.end.repr
      ((((conjEndRationalRepresentation ρ).action g :
        LinearMap.GeneralLinearGroup k (Module.End k V)) :
          Module.End k (Module.End k V)) (b.end (a, c))) (p, qidx) = _
    change b.end.repr
      (((conjEndGeneralLinear (ρ.action g) :
        LinearMap.GeneralLinearGroup k (Module.End k V)) :
          Module.End k (Module.End k V)) (b.end (a, c))) (p, qidx) = _
    rw [show conjEndGeneralLinear (ρ.action g) =
        generalLinearConjugationRepresentation (ρ.action g) by
      apply Units.ext
      rfl]
    rw [generalLinearConjugationRepresentation_matrixCoefficient]
    change _ =
      rationalRepresentationMatrixCoefficient ρ b f p a g *
        rationalRepresentationInverseMatrixCoefficient ρ b f c qidx g
    rw [rationalRepresentationMatrixCoefficient_apply ρ b f hf]
    rw [rationalRepresentationInverseMatrixCoefficient_apply ρ b f hf]
  rw [hcoefficient, D.leibniz,
    rationalRepresentationInverseMatrixCoefficient_derivation ρ b f hf]
  have hmatrix_one (r s : Fin (Module.finrank k V)) :
      rationalRepresentationMatrixCoefficient ρ b f r s 1 =
        if r = s then 1 else 0 := by
    rw [rationalRepresentationMatrixCoefficient_apply ρ b f hf, map_one]
    change b.repr (b s) r = _
    simpa [eq_comm] using Module.Basis.repr_self_apply b s r
  have hinverse_one (r s : Fin (Module.finrank k V)) :
      rationalRepresentationInverseMatrixCoefficient ρ b f r s 1 =
        if r = s then 1 else 0 := by
    rw [rationalRepresentationInverseMatrixCoefficient_apply ρ b f hf, map_one]
    change b.repr (b s) r = _
    simpa [eq_comm] using Module.Basis.repr_self_apply b s r
  have hsmul (z : G.PolynomialFunction) (d : k) : z • d = z 1 * d := rfl
  rw [hsmul, hsmul, hmatrix_one, hinverse_one]
  change _ = b.end.coord (p, qidx)
    (A * b.end (a, c) - b.end (a, c) * A)
  rw [Module.Basis.coord_apply, Module.Basis.end_repr_apply]
  simp only [map_sub]
  simp [Matrix.stdBasis, LinearMap.toMatrix_apply, Module.End.mul_apply,
    Module.Basis.end_apply_apply]
  split_ifs <;> simp_all
    [Theory.AlgebraicGroup.Module.Basis.end_apply_eq_smul]
  all_goals abel

end Theory.AlgebraicGroup.Bor1

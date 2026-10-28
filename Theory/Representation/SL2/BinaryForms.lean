module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Binary Forms for SL2

Over any field, substitution by the columns of an SL2 matrix acts covariantly
on polynomials in two variables. It preserves the subspace of homogeneous
polynomials of degree `k`, giving a representation of dimension `k + 1`.
The dimension proof identifies its monomial indices with `Fin (k + 1)`.

These are the representations denoted by Gamma^(k) in Fong--Wong, Nagoya
Math. J. 36 (1969), p. 149, formula (1.15). This module supplies their actual
construction; irreducibility in restricted degree and the tensor-product
classification are separate results. The definitions are exposed so those
proofs can compute the action on polynomial coefficients and subspaces.
-/

open Matrix MvPolynomial
open scoped MatrixGroups

namespace Representation.SL2

variable (F : Type*) [Field F]

@[expose] public noncomputable def polynomialAction (g : SL(2, F)) :
    MvPolynomial (Fin 2) F →ₐ[F] MvPolynomial (Fin 2) F :=
  MvPolynomial.aeval (fun i => ∑ j : Fin 2, C (g j i) * X j)

private theorem polynomialAction_one : polynomialAction F 1 = AlgHom.id F _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [polynomialAction, Matrix.one_apply]

private theorem polynomialAction_mul (g h : SL(2, F)) :
    polynomialAction F (g * h) = (polynomialAction F g).comp (polynomialAction F h) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [polynomialAction, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[expose] public noncomputable def polynomialRepresentation :
    Representation F SL(2, F) (MvPolynomial (Fin 2) F) where
  toFun g := (polynomialAction F g).toLinearMap
  map_one' := by exact congrArg AlgHom.toLinearMap (polynomialAction_one F)
  map_mul' g h := by exact congrArg AlgHom.toLinearMap (polynomialAction_mul F g h)

@[expose] public noncomputable def binaryForms (k : ℕ) :
    Subrepresentation (polynomialRepresentation F) where
  toSubmodule := MvPolynomial.homogeneousSubmodule (Fin 2) F k
  apply_mem_toSubmodule g := by
    intro v hv
    change (polynomialAction F g v).IsHomogeneous k
    have hvars (i : Fin 2) :
        (∑ j : Fin 2, C (g j i) * X j : MvPolynomial (Fin 2) F).IsHomogeneous 1 := by
      apply MvPolynomial.IsHomogeneous.sum
      intro j _
      exact (MvPolynomial.isHomogeneous_X F j).C_mul (g j i)
    simpa only [one_mul, polynomialAction] using (MvPolynomial.IsHomogeneous.aeval hv _ hvars)

@[expose] public noncomputable def binaryFormsRepresentation (k : ℕ) :
    Representation F SL(2, F) (MvPolynomial.homogeneousSubmodule (Fin 2) F k) :=
  (binaryForms F k).toRepresentation

public instance binaryFormsFiniteDimensional (k : ℕ) :
    FiniteDimensional F (MvPolynomial.homogeneousSubmodule (Fin 2) F k) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) F k)

private noncomputable def degreeIndicesEquiv (k : ℕ) :
    {d : Fin 2 →₀ ℕ // d.degree = k} ≃ Fin (k + 1) where
  toFun d := ⟨d.val 0, by
    have := d.property
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at this
    omega⟩
  invFun i := ⟨Finsupp.equivFunOnFinite.symm ![i.val, k - i.val], by
    simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    omega⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    fin_cases i
    · simp
    · have := d.property
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at this
      simp
      omega
  right_inv i := by apply Fin.ext; simp

public theorem binaryForms_finrank (k : ℕ) :
    Module.finrank F (binaryForms F k).toSubmodule = k + 1 := by
  classical
  let hFin : Fintype {d : Fin 2 →₀ ℕ // d.degree = k} :=
    Fintype.ofEquiv (Fin (k + 1)) (degreeIndicesEquiv k).symm
  let : Fintype {d : Fin 2 →₀ ℕ | d.degree = k} := hFin
  change Module.finrank F (MvPolynomial.homogeneousSubmodule (Fin 2) F k) = k + 1
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  rw [(AddMonoidAlgebra.supportedEquivFinsupp (R := F) (S := F)
    {d : Fin 2 →₀ ℕ | d.degree = k}).finrank_eq]
  rw [Module.finrank_finsupp_self]
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (degreeIndicesEquiv k)).trans (Nat.card_fin (k + 1))

end Representation.SL2

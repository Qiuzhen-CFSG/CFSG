module

public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Basic
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.CharP.Two

/-!
# Isometry from Hermitian determinants to the chosen minus form

Over the actual Frobenius fixed field `k`, the Hermitian determinant is
`a*b - norm(z)`. The chosen minus form is one hyperbolic plane plus the
anisotropic plane `x² + x*y - c*y²`, where `c = parameter k`.

The polynomial `X² + X - c` is irreducible by the defining property of `c`.
Its root field embeds over `k` into the existing quadratic extension, since
both extensions have degree two. A root `α` in that extension satisfies
`conjugation α = α + 1`. Thus `norm(x + y*α) = x² + x*y - c*y²`.
Anisotropy makes this coordinate map injective, and equality of dimensions
makes it a linear equivalence. Adjoining the hyperbolic coordinates gives
the isometry, preserving quadratic values in characteristic two.

This supplies the change of quadratic coordinates in the Hermitian model of
Ω₄⁻ used in Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), C.1.30, F.1.12(I)(6), and I.1.6(3),
printed pp.135, 263, and 408. It does not require the separate identification
of the orthogonal commutator subgroup with the SL₂ image.
-/

noncomputable section
namespace Representation.OrthogonalFourMinus.HermitianEquiv
open FiniteModel
open ClassicalOrthogonal.Minus (parameter parameter_spec)
open Polynomial
variable (n : ℕ) [NeZero n]

private lemma exists_parameter_root : ∃ α : Field n,
    α ^ 2 + α = (parameter (fixedField n) : Field n) := by
  let p : (fixedField n)[X] := X ^ 2 + X - C (parameter (fixedField n))
  have hd : p.natDegree = 2 := by
    dsimp [p]
    rw [natDegree_sub_C, natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · simp
  have hi : Irreducible p := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · simp [hd]
    · intro x hx
      apply parameter_spec (fixedField n) x
      simpa [p, IsRoot, sub_eq_zero] using hx
  let : Fact (Irreducible p) := ⟨hi⟩
  have he : Nonempty (AdjoinRoot p →ₐ[fixedField n] Field n) :=
    FiniteField.nonempty_algHom_of_finrank_dvd (by
      rw [(AdjoinRoot.powerBasis hi.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hd, finrank_field])
  let e := he.some
  refine ⟨e (AdjoinRoot.root p), ?_⟩
  have h := AdjoinRoot.aeval_algHom_eq_zero p e
  simp only [p, map_sub, map_add, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  exact h

private def parameterRoot : Field n := (exists_parameter_root n).choose

private lemma parameterRoot_sq_add : (parameterRoot n) ^ 2 + parameterRoot n = (parameter (fixedField n) : Field n) :=
  (exists_parameter_root n).choose_spec

private lemma parameterRoot_not_fixed : conjugation n (parameterRoot n) ≠ parameterRoot n := by
  intro h
  let a : fixedField n := ⟨parameterRoot n, h⟩
  apply parameter_spec (fixedField n) a
  apply Subtype.ext
  exact parameterRoot_sq_add n

omit [NeZero n] in
private lemma conjugation_coe (x : fixedField n) :
    conjugation n (x : Field n) = x := x.property

private lemma conjugation_parameterRoot : conjugation n (parameterRoot n) = parameterRoot n + 1 := by
  have hr := parameterRoot_sq_add n
  have hc := congrArg (conjugation n) hr
  simp only [map_add, map_pow, conjugation_coe] at hc
  have hmul : (conjugation n (parameterRoot n) - parameterRoot n) *
      (conjugation n (parameterRoot n) + parameterRoot n + 1) = 0 := by
    linear_combination hc - hr
  have hsum := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr (parameterRoot_not_fixed n))
  rw [add_assoc] at hsum
  exact CharTwo.add_eq_zero.mp hsum

private def planeToField : (fixedField n × fixedField n) →ₗ[fixedField n] Field n where
  toFun v := v.1.val + v.2.val * parameterRoot n
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Subfield.coe_add]
    ring
  map_smul' c v := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Subfield.coe_mul,
      Subfield.smul_def, RingHom.id_apply]
    ring

private lemma norm_planeToField (v : fixedField n × fixedField n) :
    FiniteModel.norm n (planeToField n v) =
      ClassicalOrthogonal.Minus.plane (fixedField n) (parameter (fixedField n)) v := by
  apply Subtype.ext
  simp only [FiniteModel.norm, planeToField, LinearMap.coe_mk, AddHom.coe_mk,
    ClassicalOrthogonal.Minus.plane_apply, Subfield.coe_sub, Subfield.coe_add,
    SubmonoidClass.coe_pow, Subfield.coe_mul, map_add, map_mul, conjugation_coe, conjugation_parameterRoot]
  rw [CharTwo.sub_eq_add]
  linear_combination v.2.val ^ 2 * parameterRoot_sq_add n +
    (v.1.val * v.2.val * parameterRoot n) * (CharTwo.two_eq_zero (R := Field n))

private lemma planeToField_injective : Function.Injective (planeToField n) := by
  intro v w h
  apply sub_eq_zero.mp
  apply ClassicalOrthogonal.Minus.plane_anisotropic (fixedField n)
    (parameter (fixedField n)) (parameter_spec (fixedField n))
  rw [← norm_planeToField, map_sub, h, sub_self]
  exact (norm_eq_zero_iff n 0).mpr rfl

private def planeFieldEquiv : (fixedField n × fixedField n) ≃ₗ[fixedField n] Field n :=
  (planeToField n).linearEquivOfInjective (planeToField_injective n) (by
    rw [Module.finrank_prod, finrank_field]
    simp)

/-- The determinant model is quadratically isometric to the existing chosen
four-dimensional minus form, including over the field of order two. -/
public def hermitianMinusIsometry :
    (FiniteModel.form n).IsometryEquiv
      (ClassicalOrthogonal.Minus.quadraticForm (fixedField n) 2) :=
  QuadraticMap.IsometryEquiv.symm
    { toLinearEquiv :=
        ((LinearEquiv.funUnique (Fin 1) (fixedField n) (fixedField n × fixedField n)).prodCongr
          (planeFieldEquiv n)).trans (coordinates n).symm
      map_app' := by
        intro v
        change FiniteModel.form n ((coordinates n).symm (v.1 0, planeToField n v.2)) = _
        rw [form_coordinates, norm_planeToField]
        simp [ClassicalOrthogonal.Minus.quadraticForm, CharTwo.sub_eq_add] }

end Representation.OrthogonalFourMinus.HermitianEquiv

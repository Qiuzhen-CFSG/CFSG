module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.Reflection

/-!
# Anisotropic reflections of quadratic spaces

For a quadratic form `Q` over a field in which `2` is invertible and a vector `v`
with `Q v != 0`, this module defines the standard reflection

`x |-> x - 2 * (Q v)⁻¹ * Q.associated v x • v`.

The construction uses `Module.reflection` with the linear functional obtained from
the polar form `Q.associated`.  The defining normalization makes the reflection send
`v` to `-v`; symmetry of the polar form and its diagonal identity prove preservation
of `Q`.  Its determinant is `-1`, by the rank-one matrix determinant formula.

This is the low-level reflection API used by the Cartan--Dieudonne factorization and
by Clifford-algebra consumers.  The construction is the anisotropic reflection in
the classical Cartan--Dieudonne theorem.
-/

open Module

namespace QuadraticForm

variable {k V : Type*} [Field k] [Invertible (2 : k)]
variable [AddCommGroup V] [Module k V]

private noncomputable def reflectionFunctional (Q : QuadraticForm k V)
    (v : V) : Module.Dual k V :=
  (2 * (Q v)⁻¹) • Q.associated v

private lemma reflectionFunctional_self (Q : QuadraticForm k V)
    {v : V} (hv : Q v ≠ 0) :
    reflectionFunctional Q v v = 2 := by
  simp [reflectionFunctional, QuadraticMap.associated_eq_self_apply k Q v, hv]

/-- The reflection in the hyperplane polar-orthogonal to an anisotropic vector. -/
public noncomputable def anisotropicReflection (Q : QuadraticForm k V)
    (v : V) (hv : Q v ≠ 0) : V ≃ₗ[k] V :=
  Module.reflection (reflectionFunctional_self Q hv)

/-- The exact action formula for an anisotropic quadratic reflection. -/
public lemma anisotropicReflection_apply (Q : QuadraticForm k V)
    (v : V) (hv : Q v ≠ 0) (x : V) :
    anisotropicReflection Q v hv x =
      x - (2 * (Q v)⁻¹ * Q.associated v x) • v := by
  rw [anisotropicReflection, Module.reflection_apply]
  rfl

@[simp]
public lemma anisotropicReflection_apply_self (Q : QuadraticForm k V)
    (v : V) (hv : Q v ≠ 0) :
    anisotropicReflection Q v hv v = -v := by
  exact Module.reflection_apply_self (reflectionFunctional_self Q hv)

/-- An anisotropic reflection is an involution. -/
public lemma anisotropicReflection_involutive (Q : QuadraticForm k V)
    (v : V) (hv : Q v ≠ 0) :
    Function.Involutive (anisotropicReflection Q v hv) := by
  exact Module.involutive_reflection (reflectionFunctional_self Q hv)

@[simp]
public lemma anisotropicReflection_symm (Q : QuadraticForm k V)
    (v : V) (hv : Q v ≠ 0) :
    (anisotropicReflection Q v hv).symm = anisotropicReflection Q v hv := by
  exact Module.reflection_symm (reflectionFunctional_self Q hv)

/-- An anisotropic reflection preserves the quadratic form. -/
public lemma anisotropicReflection_preserves (Q : QuadraticForm k V)
    (v : V) (hv : Q v ≠ 0) (x : V) :
    Q (anisotropicReflection Q v hv x) = Q x := by
  rw [← QuadraticMap.associated_eq_self_apply k Q]
  simp only [anisotropicReflection_apply, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply]
  rw [QuadraticMap.associated_eq_self_apply k Q x,
    QuadraticMap.associated_eq_self_apply k Q v]
  rw [QuadraticMap.associated_isSymm k Q x v]
  have hcancel : Q v * (Q v)⁻¹ ^ 2 = (Q v)⁻¹ := by
    calc
      _ = (Q v * (Q v)⁻¹) * (Q v)⁻¹ := by ring
      _ = _ := by rw [mul_inv_cancel₀ hv, one_mul]
  ring_nf at hcancel ⊢
  rw [hcancel]
  ring

/-- The determinant of an anisotropic reflection is `-1`. -/
public lemma anisotropicReflection_det [FiniteDimensional k V]
    (Q : QuadraticForm k V) (v : V) (hv : Q v ≠ 0) :
    LinearEquiv.det (anisotropicReflection Q v hv) = -1 := by
  let b := Module.finBasis k V
  let f := reflectionFunctional Q v
  have hf : f v = 2 := reflectionFunctional_self Q hv
  have hdot : (f ∘ b) ⬝ᵥ (b.repr v) = f v := by
    simp only [dotProduct, Function.comp_apply]
    calc
      _ = ∑ i, f ((b.repr v i) • b i) := by
        apply Finset.sum_congr rfl
        intro i _
        simp [mul_comm]
      _ = f (∑ i, (b.repr v i) • b i) := by rw [map_sum]
      _ = f v := by rw [b.sum_repr]
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix b]
  change Matrix.det (LinearMap.toMatrix b b (LinearMap.id - f.smulRight v)) = _
  rw [map_sub, LinearMap.toMatrix_id, LinearMap.toMatrix_smulRight,
    sub_eq_add_neg, ← Matrix.neg_vecMulVec, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [hdot, hf]
  ring

/-- The ordered product of anisotropic reflections indexed by a list of anisotropic vectors. -/
public noncomputable def anisotropicReflectionsProduct (Q : QuadraticForm k V)
    (vs : List {v : V // Q v ≠ 0}) : V ≃ₗ[k] V :=
  (vs.map fun (v : {v : V // Q v ≠ 0}) =>
    anisotropicReflection Q v.val v.property).prod

@[simp]
public lemma anisotropicReflectionsProduct_nil (Q : QuadraticForm k V) :
    anisotropicReflectionsProduct Q [] = 1 := by
  rfl

@[simp]
public lemma anisotropicReflectionsProduct_cons (Q : QuadraticForm k V)
    (v : {v : V // Q v ≠ 0}) (vs : List {v : V // Q v ≠ 0}) :
    anisotropicReflectionsProduct Q (v :: vs) =
      anisotropicReflection Q (v : V) v.property * anisotropicReflectionsProduct Q vs := by
  rfl

/-- A product of anisotropic reflections preserves the quadratic form. -/
public lemma anisotropicReflectionsProduct_preserves (Q : QuadraticForm k V)
    (vs : List {v : V // Q v ≠ 0}) (x : V) :
    Q (anisotropicReflectionsProduct Q vs x) = Q x := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      change Q (anisotropicReflection Q (v : V) v.property
        (anisotropicReflectionsProduct Q vs x)) = Q x
      rw [anisotropicReflection_preserves, ih]

/-- The determinant of a product of anisotropic reflections records the list parity. -/
public lemma anisotropicReflectionsProduct_det [FiniteDimensional k V]
    (Q : QuadraticForm k V) (vs : List {v : V // Q v ≠ 0}) :
    LinearEquiv.det (anisotropicReflectionsProduct Q vs) =
      (-1 : kˣ) ^ vs.length := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
      rw [anisotropicReflectionsProduct_cons, map_mul,
        anisotropicReflection_det, ih, List.length_cons, pow_succ]
      exact mul_comm _ _

/-- A determinant-one product of anisotropic reflections has even length. -/
public lemma even_length_of_anisotropicReflectionsProduct_det_eq_one
    [FiniteDimensional k V] (Q : QuadraticForm k V)
    (vs : List {v : V // Q v ≠ 0})
    (hdet : LinearEquiv.det (anisotropicReflectionsProduct Q vs) = 1) :
    Even vs.length := by
  rw [anisotropicReflectionsProduct_det] at hdet
  apply (neg_one_pow_eq_one_iff_even ?_).mp hdet
  intro h
  have h' : (-1 : k) = 1 := congrArg Units.val h
  apply two_ne_zero (α := k)
  linear_combination -h'

end QuadraticForm

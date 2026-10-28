module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Ring

/-!
# Characteristic polynomials and semisimplicity for SL₃

The characteristic polynomial of a determinant-one matrix of size three is
`X³ - trace(g) X² + trace(g⁻¹) X - 1`. Thus two field elements determine it,
including in characteristic two. Prime-to-characteristic order gives the
separable annihilator `Xⁿ - 1` and hence semisimplicity; the characteristic
polynomial itself need not be squarefree.

These are the parameter and semisimplicity steps in counting actual regular
conjugacy classes of SL₃. Source context: GLS III, 2.8.2 and 2.8.6(a),
`refs/KGroup/GLS3/chapter2.tex`. No representation catalogue is assumed.
-/

namespace Theory.SpecificGroups.SL3.PRegularClasses

open Polynomial

variable {F : Type*} [Field F]

private theorem matrix_charpoly_eq_cubic (A : Matrix (Fin 3) (Fin 3) F) :
    A.charpoly = X ^ 3 - C A.trace * X ^ 2 + C A.adjugate.trace * X - C A.det := by
  simp only [Matrix.charpoly, Matrix.det_fin_three, Matrix.charmatrix_apply_eq,
    Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.adjugate_fin_three]
  simp
  ring

/-- The two traces give every nonconstant coefficient of the monic cubic. -/
public theorem charpoly_eq_cubic (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    g.val.charpoly = X ^ 3 - C g.val.trace * X ^ 2 + C (g⁻¹).val.trace * X - 1 := by
  rw [matrix_charpoly_eq_cubic, Matrix.SpecialLinearGroup.coe_inv, g.property, map_one]

/-- Matching traces of the matrices and their inverses match the characteristic
polynomials, without any regularity or field-size restriction. -/
public theorem charpoly_eq_of_trace_eq (g h : Matrix.SpecialLinearGroup (Fin 3) F)
    (ht : g.val.trace = h.val.trace) (hi : (g⁻¹).val.trace = (h⁻¹).val.trace) :
    g.val.charpoly = h.val.charpoly := by
  rw [charpoly_eq_cubic g, charpoly_eq_cubic h, ht, hi]

/-- Prime-to-characteristic elements act semisimply on the natural module. -/
public theorem isSemisimple_of_pRegular {p : ℕ} [CharP F p]
    (g : Matrix.SpecialLinearGroup (Fin 3) F) (hg : ¬ p ∣ orderOf g) :
    Module.End.IsSemisimple (Matrix.toLin' g.val) := by
  let e : Matrix (Fin 3) (Fin 3) F ≃ₐ[F] Module.End F (Fin 3 → F) := Matrix.toLinAlgEquiv'
  have hpow : g.val ^ orderOf g = 1 := by
    simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] using
      congrArg (fun h : Matrix.SpecialLinearGroup (Fin 3) F => h.val) (pow_orderOf_eq_one g)
  change (e g.val).IsSemisimple
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C' p (orderOf g) (1 : F) hg one_ne_zero).squarefree
  simp only [map_sub, Polynomial.aeval_X_pow, map_one]
  rw [← map_pow, hpow, map_one, sub_self]

end Theory.SpecificGroups.SL3.PRegularClasses

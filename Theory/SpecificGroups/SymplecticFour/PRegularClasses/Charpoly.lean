module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Characteristic polynomials of symplectic four-space

The inverse of a symplectic matrix is similar to its transpose. Since its
determinant is one, its characteristic polynomial is reciprocal. In dimension
four it therefore has the form `X⁴ + aX³ + bX² + aX + 1`, over any field.
In characteristic two, odd-order elements act semisimply because their
annihilating polynomial `Xⁿ - 1` is separable.

These are linear-algebra inputs to the odd-order conjugacy-class bound used in
the concrete Sp₄ module catalogue. They do not assert conjugacy from equality
of characteristic polynomials. Source context: GLS III, 2.8.2, 2.8.6(a), and
Examples 2.8.10(d), `refs/KGroup/GLS3/chapter2.tex`; Aschbacher--Smith,
`refs/quasithin.pdf`, proof of G.9.3, printed pp.356--357.
-/

namespace Theory.SpecificGroups.SymplecticFour.PRegularClasses

open Matrix Polynomial

variable {F : Type*} [Field F]
local notation "Sp" => Matrix.symplecticGroup (Fin 2) F

private theorem charpoly_inverse (g : Sp) :
    (g⁻¹).val.charpoly = g.val.charpoly := by
  rw [SymplecticGroup.coe_inv, charpoly_mul_comm, ← Matrix.mul_assoc]
  simp [Matrix.J_squared]

/-- The actual symplectic matrix has a reciprocal characteristic polynomial. -/
public theorem charpoly_reverse (g : Sp) :
    g.val.charpoly.reverse = g.val.charpoly := by
  have hi := charpoly_inverse g
  rw [SymplecticGroup.coe_inv', Matrix.charpoly_inv g.val
    ((Matrix.isUnit_iff_isUnit_det _).mpr (SymplecticGroup.symplectic_det g.property))] at hi
  norm_num [SymplecticGroup.det_eq_one g.property, ← Matrix.reverse_charpoly] at hi
  exact hi

private theorem charpoly_coeff_one (g : Sp) :
    g.val.charpoly.coeff 1 = g.val.charpoly.coeff 3 := by
  have h := congrArg (fun p : F[X] => p.coeff 1) (charpoly_reverse g)
  simpa [Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
    Polynomial.revAt_le] using h.symm

private theorem charpoly_coeff_zero (g : Sp) : g.val.charpoly.coeff 0 = 1 := by
  have h := Matrix.det_eq_sign_charpoly_coeff g.val
  norm_num [SymplecticGroup.det_eq_one g.property] at h
  exact h.symm

private theorem charpoly_coeff_four (g : Sp) : g.val.charpoly.coeff 4 = 1 := by
  simpa [Matrix.charpoly_natDegree_eq_dim] using g.val.charpoly_monic.coeff_natDegree

/-- Only the cubic and quadratic coefficients of a symplectic quartic are free. -/
public theorem charpoly_eq_quartic (g : Sp) :
    g.val.charpoly = X ^ 4 + C (g.val.charpoly.coeff 3) * X ^ 3 +
      C (g.val.charpoly.coeff 2) * X ^ 2 + C (g.val.charpoly.coeff 3) * X + 1 := by
  ext n
  by_cases hn : n ≤ 4
  · interval_cases n <;>
      simp [coeff_add, coeff_C_mul, coeff_X_pow, coeff_one, charpoly_coeff_zero,
        charpoly_coeff_one, charpoly_coeff_four]
  · have hlt : g.val.charpoly.natDegree < n := by
      simp only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_sum, Fintype.card_fin]
      omega
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn4 : n ≠ 4 := by omega
    simp [coeff_eq_zero_of_natDegree_lt hlt, coeff_X, coeff_one,
      hn0, Ne.symm hn1, hn2, hn3, hn4]

/-- Equality of the two free coefficients determines the whole polynomial. -/
public theorem charpoly_eq_of_coefficients_eq (g h : Sp)
    (h3 : g.val.charpoly.coeff 3 = h.val.charpoly.coeff 3)
    (h2 : g.val.charpoly.coeff 2 = h.val.charpoly.coeff 2) :
    g.val.charpoly = h.val.charpoly := by
  rw [charpoly_eq_quartic g, charpoly_eq_quartic h, h3, h2]

/-- Odd-order symplectic elements in characteristic two act semisimply,
including those with repeated characteristic-polynomial factors. -/
public theorem isSemisimple_of_odd_order [CharP F 2] (g : Sp)
    (hg : ¬ 2 ∣ orderOf g) : Module.End.IsSemisimple (Matrix.toLin' g.val) := by
  let e : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F ≃ₐ[F]
      Module.End F ((Fin 2 ⊕ Fin 2) → F) := Matrix.toLinAlgEquiv'
  change (e g.val).IsSemisimple
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C' 2 (orderOf g) (1 : F) hg one_ne_zero).squarefree
  have hpow : g.val ^ orderOf g = 1 := congrArg Subtype.val (pow_orderOf_eq_one g)
  simp only [map_sub, Polynomial.aeval_X_pow, map_one]
  rw [← map_pow, hpow, map_one, sub_self]

end Theory.SpecificGroups.SymplecticFour.PRegularClasses

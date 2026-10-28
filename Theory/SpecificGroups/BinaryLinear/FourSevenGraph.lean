module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Seven-elements and graph automorphisms of GL₄(2)

An element fixed by an inner twist of inverse transpose has reciprocal
characteristic polynomial. The four reciprocal monic quartics over F₂
have gcd X+1 with X⁷+1. The displayed Bézout identities and Cayley--Hamilton
therefore force a fixed element with seventh power one to be the identity.
The proof adapts the degree-five calculation in `FiveSevenGraph` and retains
the actual special-linear/matrix/linear-map equivalences.

Source: the binary action in Aschbacher--Smith, 12.9, printed pp.862--864.
-/

open Polynomial Matrix
open scoped MatrixGroups
namespace BinaryLinear.FourSevenGraph

private noncomputable def reciprocalQuartic (a b : ZMod 2) : Polynomial (ZMod 2) :=
  X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C a * X + 1

private theorem binary_value (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem quartic_bezout (a b : ZMod 2) :
    ∃ r s : Polynomial (ZMod 2),
      r * reciprocalQuartic a b + s * (X ^ 7 + 1) = X + 1 := by
  have htwo : (2 : Polynomial (ZMod 2)) = 0 := CharP.cast_eq_zero _ 2
  have hfour : (4 : Polynomial (ZMod 2)) = 0 := by
    calc
      (4 : Polynomial (ZMod 2)) = 2 + 2 := by norm_num
      _ = 0 := by rw [htwo]; simp
  have hthree : (3 : Polynomial (ZMod 2)) = 1 := by
    calc
      (3 : Polynomial (ZMod 2)) = 2 + 1 := by norm_num
      _ = 1 := by rw [htwo]; simp
  rcases binary_value a with rfl | rfl <;> rcases binary_value b with rfl | rfl
  · refine ⟨X ^ 4 + 1, X, ?_⟩
    simp only [reciprocalQuartic, C_0, zero_mul, add_zero]
    ring_nf
    simp [htwo]
  · refine ⟨X ^ 7 + X ^ 3 + X + 1, X ^ 4 + X ^ 2, ?_⟩
    simp only [reciprocalQuartic, C_0, C_1, zero_mul, one_mul, add_zero]
    ring_nf
    simp [htwo]
  · refine ⟨X ^ 3 + X ^ 2 + X, 1, ?_⟩
    simp only [reciprocalQuartic, C_0, C_1, zero_mul, one_mul, add_zero]
    ring_nf
    simp [htwo]
  · refine ⟨X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X + 1, X ^ 3 + X, ?_⟩
    simp only [reciprocalQuartic, C_1, one_mul]
    ring_nf
    simp [htwo, hthree, hfour]

private theorem quartic_expansion (q : Polynomial (ZMod 2))
    (hm : q.Monic) (hd : q.natDegree = 4) (hr : q.reverse = q) :
    q = reciprocalQuartic (q.coeff 3) (q.coeff 2) := by
  have h4 : q.coeff 4 = 1 := by simpa only [hd] using hm.coeff_natDegree
  have hc (i : ℕ) (hi : i ≤ 4) : q.coeff i = q.coeff (4-i) := by
    conv_lhs => rw [← hr]
    rw [coeff_reverse, hd, revAt_le hi]
  have h0 : q.coeff 0 = 1 := (hc 0 (by decide)).trans h4
  have h1 : q.coeff 1 = q.coeff 3 := hc 1 (by decide)
  conv_lhs => rw [q.as_sum_range_C_mul_X_pow, hd]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, mul_one, h4, h0, h1, C_1, one_mul]
  dsimp [reciprocalQuartic]
  ring

private theorem matrix_eq_one (A : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hp : A ^ 7 = 1) (hr : A.charpoly.reverse = A.charpoly) : A = 1 := by
  have hq := quartic_expansion A.charpoly (Matrix.charpoly_monic A)
    (by simp) hr
  obtain ⟨r, s, hbez⟩ := quartic_bezout (A.charpoly.coeff 3) (A.charpoly.coeff 2)
  rw [← hq] at hbez
  have hann := Matrix.aeval_self_charpoly A
  have hseven : aeval A (X ^ 7 + 1 : Polynomial (ZMod 2)) = 0 := by
    simp only [map_add, map_pow, aeval_X, map_one, hp]
    ext i j
    exact CharTwo.add_self_eq_zero _
  have he := congrArg (aeval A) hbez
  simp only [map_add, map_mul, aeval_X, map_one, hann, hseven, mul_zero, zero_add] at he
  have htwo : (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) + 1 = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero _
  exact add_right_cancel (he.symm.trans htwo.symm)

open OuterCyclic

private theorem sl_charpoly_conj (g x : SL(4, ZMod 2)) :
    ((MulAut.conj g x : SL(4, ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).charpoly =
      (x : Matrix (Fin 4) (Fin 4) (ZMod 2)).charpoly := by
  change ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) * x *
    adjugate (g : Matrix (Fin 4) (Fin 4) (ZMod 2))).charpoly = _
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, Matrix.adjugate_mul,
    Matrix.SpecialLinearGroup.det_coe, one_smul, one_mul]

private theorem sl_charpoly_graph (x : SL(4, ZMod 2)) :
    ((graphSL 4 x : SL(4, ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).charpoly =
      (x : Matrix (Fin 4) (Fin 4) (ZMod 2)).charpoly.reverse := by
  have hi : IsUnit ((x : Matrix (Fin 4) (Fin 4) (ZMod 2)).transpose) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose,
      Matrix.SpecialLinearGroup.det_coe]
    exact isUnit_one
  have hinv : (Matrix.SpecialLinearGroup.transpose x)⁻¹ =
      ((x : Matrix (Fin 4) (Fin 4) (ZMod 2)).transpose)⁻¹ := by
    rw [Matrix.inv_def, Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe]
    simp
  change (↑((Matrix.SpecialLinearGroup.transpose x)⁻¹) :
    Matrix (Fin 4) (Fin 4) (ZMod 2)).charpoly = _
  rw [hinv, Matrix.charpoly_inv _ hi, ← Matrix.reverse_charpoly,
    Matrix.charpoly_transpose, Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe]
  simp [CharTwo.neg_eq]

/-- In degree four over the binary field, an inner twist of inverse transpose
fixes no nonidentity element whose seventh power is one. -/
public theorem graph_fixed_seven_eq_one (g x : LinearGroup 4)
    (hp : x ^ 7 = 1) (hf : (graphLinear 4 * MulAut.conj g) x = x) : x = 1 := by
  let e := slEquivLinear 4
  let y := e.symm x
  let k := e.symm g
  have hsl : graphSL 4 (MulAut.conj k y) = y := by
    apply e.injective
    simpa [e, y, k, graphLinear, MulAut.congr_apply, MulAut.mul_apply,
      MulAut.conj_apply] using hf
  have hconj : MulAut.conj k y = graphSL 4 y := by
    have he := congrArg (graphSL 4) hsl
    have hh : graphSL 4 (graphSL 4 (MulAut.conj k y)) = MulAut.conj k y := by
      simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using congrArg (fun a : MulAut SL(4, ZMod 2) => a (MulAut.conj k y)) (graphSL_sq 4)
    exact hh.symm.trans he
  have hr : (y : Matrix (Fin 4) (Fin 4) (ZMod 2)).charpoly.reverse =
      (y : Matrix (Fin 4) (Fin 4) (ZMod 2)).charpoly := by
    rw [← sl_charpoly_graph, ← hconj, sl_charpoly_conj]
  have hy : y ^ 7 = 1 := by
    dsimp [y]
    rw [← map_pow, hp, map_one]
  have hm : (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) ^ 7 = 1 :=
    congrArg (fun z : SL(4, ZMod 2) => (z : Matrix (Fin 4) (Fin 4) (ZMod 2))) hy
  have hy1 : y = 1 := Subtype.ext (matrix_eq_one _ hm hr)
  have he := congrArg e hy1
  simpa [y] using he

end BinaryLinear.FourSevenGraph

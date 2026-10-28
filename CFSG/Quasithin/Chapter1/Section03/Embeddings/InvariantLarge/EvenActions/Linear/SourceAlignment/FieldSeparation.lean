module

public import Theory.SpecificGroups.PSL3.CartanActions

/-!
# Separating genuine field and inner-diagonal automorphisms

In the actual PSL₃ quotient in characteristic two, every elementary matrix
has trace one. Thus equality of two such projective matrices under linear
conjugation lifts without a scalar ambiguity. A linear conjugation which is
also a coefficient-field automorphism fixes all elementary matrices with
coefficient one. Its matrix commutes with every off-diagonal matrix unit,
hence is scalar and induces the identity.

This proves the disjointness needed before removing the field factor in
A.3.15(5); it assumes neither Cartan containment nor an automorphism
classification. Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
A.3.15(5), printed pp.50–51; GLS3, §§2.5 and 2.7.
-/

public section

open scoped MatrixGroups
open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear.SourceAlignment

variable (E : Type*) [Field E] [CharP E 2]

private theorem trace_transvection {i j : Fin 3} (hij : i ≠ j) (a : E) :
    Matrix.trace (Matrix.SpecialLinearGroup.transvection hij a).val = 1 := by
  change Matrix.trace (Matrix.transvection i j a) = 1
  have hthree : (3 : E) = 1 := by
    calc
      (3 : E) = 1 + 1 + 1 := by ring
      _ = 1 := by rw [CharTwo.add_self_eq_zero, zero_add]
  simpa [Matrix.transvection, hij] using hthree

omit [CharP E 2] in

private theorem lift_eq_of_trace_one (x y : SL(3,E))
    (hx : Matrix.trace x.val = 1) (hy : Matrix.trace y.val = 1)
    (h : projection E x = projection E y) : x = y := by
  have hc := (projection E).eq_iff.mp h
  rw [projection_ker] at hc
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have he : x.val = r • y.val := by
    calc
      x.val = (y * (y⁻¹ * x)).val := by simp only [mul_inv_cancel_left]
      _ = y.val * Matrix.scalar (Fin 3) r := by rw [Matrix.SpecialLinearGroup.coe_mul, ← hr]
      _ = r • y.val := by
        ext i j
        simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]
  have hr1 : r = 1 := by
    rw [he, Matrix.trace_smul, hy, smul_eq_mul, mul_one] at hx
    exact hx
  exact Subtype.ext (by simpa [hr1] using he)

/-- The actual coefficient-field subgroup intersects the inner-diagonal group trivially. -/
theorem field_inner_disjoint :
    Disjoint (fieldAction E).range (innerDiagonal E) := by
  apply Subgroup.disjoint_def.mpr
  rintro α ⟨σ, rfl⟩ ⟨g, hg⟩
  have hfix (i j : Fin 3) (hij : i ≠ j) :
      linearConjSL E g (Matrix.SpecialLinearGroup.transvection hij 1) =
        Matrix.SpecialLinearGroup.transvection hij 1 := by
    apply lift_eq_of_trace_one E
    · have he := congrArg Units.val
        (linearConjSL_toGL E g (Matrix.SpecialLinearGroup.transvection hij 1))
      change (linearConjSL E g (Matrix.SpecialLinearGroup.transvection hij 1)).val =
        g.val * (Matrix.SpecialLinearGroup.transvection hij 1).val * (g⁻¹).val at he
      rw [he, Matrix.trace_units_conj]
      exact trace_transvection E hij 1
    · exact trace_transvection E hij 1
    · change linearConj E g (QuotientGroup.mk _) = QuotientGroup.mk _
      rw [hg, fieldAction_mk]
      congr 1
      apply Subtype.ext
      ext k l
      change σ ((Matrix.transvection i j (1 : E)) k l) =
        (Matrix.transvection i j (1 : E)) k l
      simp [Matrix.transvection, Matrix.single, Matrix.one_apply]
  have hscalar : g.val ∈ Set.range (Matrix.scalar (Fin 3)) := by
    apply Matrix.mem_range_scalar_of_commute_single
    intro i j hij
    have he := linearConjSL_toGL E g (Matrix.SpecialLinearGroup.transvection hij 1)
    rw [hfix i j hij] at he
    have hc := mul_inv_eq_iff_eq_mul.mp he.symm
    have hm := congrArg Units.val hc
    change g.val * Matrix.transvection i j 1 = Matrix.transvection i j 1 * g.val at hm
    exact (show single i j (1 : E) * g.val = g.val * single i j 1 by
      simpa only [Matrix.transvection, mul_add, add_mul, mul_one, one_mul,
        add_right_inj] using hm.symm)
  obtain ⟨r, hr⟩ := hscalar
  rw [← hg]
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := projection_surjective E x
  change QuotientGroup.mk (linearConjSL E g y) = QuotientGroup.mk y
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL]
  have hc : g * Matrix.SpecialLinearGroup.toGL y = Matrix.SpecialLinearGroup.toGL y * g := by
    apply Units.ext
    change g.val * y.val = y.val * g.val
    rw [← hr]
    exact (Matrix.scalar_commute r (Commute.all r) y.val).eq
  rw [hc, mul_inv_cancel_right]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear.SourceAlignment

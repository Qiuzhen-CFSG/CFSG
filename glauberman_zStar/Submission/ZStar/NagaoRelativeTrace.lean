import Submission.ZStar.NagaoTrace

/-!
# Relative-trace support for the involution section

This file isolates the algebraic part of Nagao's argument.  The local
projective input is expressed through a finite free module over the order-two
group algebra.  The odd-order trace rigidity proved in `NagaoTrace` then
forces the trace on the nontrivial involution section to vanish.
-/

noncomputable section

open scoped BigOperators

namespace Submission.ZStar

namespace NagaoRelativeTrace

open Module

universe u v w

attribute [local instance] Fintype.ofFinite

/-! First, the two evaluations of an order-two group algebra differ by twice
the coefficient at its nonidentity element. -/

lemma evalPlus_sub_evalMinus_eq_two_mul_coeff
    {R C : Type*} [CommRing R] [CommGroup C] [DecidableEq C]
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hall : ∀ g : C, g = 1 ∨ g = c)
    (a : MonoidAlgebra R C) :
    NagaoTrace.evalPlus R C a -
        NagaoTrace.evalMinus c hc hc2 hall a =
      (2 : R) * a c := by
  induction a using MonoidAlgebra.induction_linear with
  | zero =>
      have hz : (0 : MonoidAlgebra R C) c = 0 := rfl
      rw [map_zero, map_zero, hz]
      ring
  | add a b ha hb =>
      rw [map_add, map_add]
      change _ = 2 * (a c + b c)
      linear_combination ha + hb
  | single g r =>
      rcases hall g with hg | hg
      · subst g
        simp [NagaoTrace.evalPlus_single, NagaoTrace.evalMinus_single, hc]
      · have hg_ne : g ≠ 1 := by
          intro h
          exact hc (hg.symm.trans h)
        rw [NagaoTrace.evalPlus_single, NagaoTrace.evalMinus_single,
          NagaoTrace.cardTwoSign_apply_of_ne_one c hc hc2 hall hg_ne]
        simp [hg, hg_ne]
        ring

/-! Trace of left multiplication on a two-element group algebra. -/

lemma trace_mulLeft_eq_two_mul_coeff_one
    {R C : Type*} [CommRing R] [CommGroup C] [Finite C]
    (hC : Nat.card C = 2) (a : MonoidAlgebra R C) :
    LinearMap.trace R (MonoidAlgebra R C)
        (LinearMap.mulLeft R a) = (2 : R) * a 1 := by
  classical
  obtain ⟨c, hc, hc_unique⟩ := (Nat.card_eq_two_iff' (1 : C)).mp hC
  have hall (g : C) : g = 1 ∨ g = c := by
    by_cases hg : g = 1
    · exact Or.inl hg
    · exact Or.inr (hc_unique g hg)
  have hc2 : c * c = 1 := by
    rcases hall (c * c) with h | h
    · exact h
    · exfalso
      apply hc
      apply mul_left_cancel (a := c)
      simpa using h
  let b : Basis C R (MonoidAlgebra R C) := Finsupp.basisSingleOne
  rw [LinearMap.trace_eq_matrix_trace R b, Matrix.trace]
  have hdiag (g : C) :
      ((LinearMap.toMatrix b b) (LinearMap.mulLeft R a)).diag g =
        a (g * g⁻¹) := by
    change Algebra.leftMulMatrix b a g g = a (g * g⁻¹)
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    change (a * MonoidAlgebra.single g 1 : MonoidAlgebra R C) g = _
    rw [MonoidAlgebra.mul_single_apply]
    simp
  simp_rw [hdiag]
  simp only [mul_inv_cancel, Finset.sum_const, Finset.card_univ,
    Fintype.card_eq_nat_card, hC]
  norm_num

/-! A finite free module over the order-two group algebra.  The next theorem
identifies the underlying `R`-trace of `c*T` with the difference of the two
specialized matrix traces. -/

theorem trace_generator_mul_of_free_groupAlgebra
    {R C M : Type*} [CommRing R] [CommGroup C] [Finite C]
    [DecidableEq C]
    [AddCommGroup M] [Module R M]
    [Module (MonoidAlgebra R C) M]
    [IsScalarTower R (MonoidAlgebra R C) M]
    [Module.Free (MonoidAlgebra R C) M]
    [Module.Finite (MonoidAlgebra R C) M]
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hall : ∀ g : C, g = 1 ∨ g = c)
    (T : M →ₗ[MonoidAlgebra R C] M) :
    LinearMap.trace R M
        ((((Algebra.lsmul R (MonoidAlgebra R C) M)
            (MonoidAlgebra.of R C c)).restrictScalars R).comp
          (T.restrictScalars R)) =
      Matrix.trace
          ((T.toMatrix (Module.Free.chooseBasis (MonoidAlgebra R C) M)
            (Module.Free.chooseBasis (MonoidAlgebra R C) M)).map
              (NagaoTrace.evalPlus R C)) -
        Matrix.trace
          ((T.toMatrix (Module.Free.chooseBasis (MonoidAlgebra R C) M)
            (Module.Free.chooseBasis (MonoidAlgebra R C) M)).map
              (NagaoTrace.evalMinus c hc hc2 hall)) := by
  classical
  let bC : Basis C R (MonoidAlgebra R C) := Finsupp.basisSingleOne
  let bM : Basis (Module.Free.ChooseBasisIndex (MonoidAlgebra R C) M)
      (MonoidAlgebra R C) M := Module.Free.chooseBasis (MonoidAlgebra R C) M
  let L : M →ₗ[MonoidAlgebra R C] M :=
    (Algebra.lsmul R (MonoidAlgebra R C) M) (MonoidAlgebra.of R C c)
  let U : M →ₗ[MonoidAlgebra R C] M := L.comp T
  have hcomp :
      (((Algebra.lsmul R (MonoidAlgebra R C) M)
          (MonoidAlgebra.of R C c)).restrictScalars R).comp
          (T.restrictScalars R) = U.restrictScalars R := by
    ext x
    rfl
  rw [hcomp, LinearMap.trace_eq_matrix_trace R (bC.smulTower' bM)]
  rw [LinearMap.restrictScalars_toMatrix bC bM U]
  simp only [Matrix.trace, Matrix.comp_apply, Matrix.map_apply,
    Fintype.sum_prod_type]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Matrix.diag_apply, Matrix.comp_apply, Matrix.map_apply]
  rw [evalPlus_sub_evalMinus_eq_two_mul_coeff c hc hc2 hall]
  let a : MonoidAlgebra R C := (T.toMatrix bM bM) i i
  have hUii : (U.toMatrix bM bM) i i =
      MonoidAlgebra.of R C c * a := by
    rw [LinearMap.toMatrix_apply]
    dsimp [U, L]
    simp only [LinearMap.comp_apply, Algebra.lsmul_apply, map_smul]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    dsimp [a]
    rw [LinearMap.toMatrix_apply]
  rw [hUii]
  have hc_inv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hcoeff : (MonoidAlgebra.of R C c * a) 1 = a c := by
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply]
    simp [hc_inv]
  calc
    (∑ j : C,
        Algebra.leftMulMatrix bC (MonoidAlgebra.of R C c * a) j j) =
        (2 : R) * (MonoidAlgebra.of R C c * a) 1 := by
      have h := trace_mulLeft_eq_two_mul_coeff_one
        (R := R) (C := C)
        (by
          exact (Nat.card_eq_two_iff' (1 : C)).mpr
            ⟨c, hc, fun x hx => (hall x).resolve_left hx⟩)
        (MonoidAlgebra.of R C c * a)
      rw [LinearMap.trace_eq_matrix_trace R bC, Matrix.trace] at h
      exact h
    _ = (2 : R) * a c := by
      rw [hcoeff]

end NagaoRelativeTrace

end Submission.ZStar

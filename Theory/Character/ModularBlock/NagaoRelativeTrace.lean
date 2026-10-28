module

public import Theory.Character.ModularBlock.NagaoTrace

/-!
# Relative-trace support for the involution section

The scalar trace of the cyclic generator followed by a group-algebra-linear
endomorphism of a finite free module is the difference between its trivial
and sign matrix traces. The proof specializes the basis trace formula from
NagaoTrace, retaining the algebra-action interface used by the relative-trace
argument. A direct canonical-basis calculation also gives twice the identity
coefficient as the trace of left multiplication on the two-element group
algebra. Subsequent odd-order rigidity makes the difference vanish.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/NagaoRelativeTrace.lean` (revision `c3503435`); the two
repeated evaluation and generator calculations reuse the proved NagaoTrace
interfaces with the exact historical statements.
-/

public section

noncomputable section

open scoped BigOperators

namespace ModularBlock

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
      (2 : R) * a.coeff c := by
  exact NagaoTrace.evalPlus_sub_evalMinus_eq_two_mul_coeff c hc hc2 hall a

/-! Trace of left multiplication on a two-element group algebra. -/

lemma trace_mulLeft_eq_two_mul_coeff_one
    {R C : Type*} [CommRing R] [CommGroup C] [Finite C]
    (hC : Nat.card C = 2) (a : MonoidAlgebra R C) :
    LinearMap.trace R (MonoidAlgebra R C)
        (LinearMap.mulLeft R a) = (2 : R) * a.coeff 1 := by
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
  let b : Basis C R (MonoidAlgebra R C) := MonoidAlgebra.basis _ _
  rw [LinearMap.trace_eq_matrix_trace R b, Matrix.trace]
  have hdiag (g : C) :
      ((LinearMap.toMatrix b b) (LinearMap.mulLeft R a)).diag g =
        a.coeff (g * g⁻¹) := by
    change Algebra.leftMulMatrix b a g g = a.coeff (g * g⁻¹)
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    change (a * MonoidAlgebra.single g 1 : MonoidAlgebra R C).coeff g = _
    rw [MonoidAlgebra.coeff_mul_single_apply]
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
  have hC : Nat.card C = 2 :=
    (Nat.card_eq_two_iff' (1 : C)).mpr
      ⟨c, hc, fun x hx => (hall x).resolve_left hx⟩
  exact NagaoTrace.trace_lsmul_comp_eq_evalPlus_sub_evalMinus
    (Module.Free.chooseBasis (MonoidAlgebra R C) M) c hc hc2 hC hall T

end NagaoRelativeTrace

end ModularBlock


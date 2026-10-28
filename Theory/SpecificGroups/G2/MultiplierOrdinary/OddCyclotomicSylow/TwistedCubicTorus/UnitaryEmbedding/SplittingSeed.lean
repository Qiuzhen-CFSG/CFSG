module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryEmbedding.Action

/-!
# Finite-field coordinates for splitting the unitary octonion algebra

Surjectivity of the quadratic field norm supplies t with t σ(t) = -1.
In odd characteristic this gives the explicit nontrivial idempotent
`(1/2, (t/2,0,0))`. Nontriviality of the degree-two Frobenius separately
supplies a nonzero trace-zero coordinate. These are the field inputs for
an explicit Peirce basis of the eight-dimensional algebra; this module
does not assume or assert the completed split-algebra comparison.

Source application: the unitary subsystem route to Aschbacher–Smith
I.1.2–I.1.4 and GLS III §6.1. Multiplication is the restriction verified
in `Action` from the licensed ATLAS split-octonion table.
-/

@[expose] public section

open Matrix Atlas.SplitOctonion
namespace Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryEmbedding
noncomputable section
variable (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- The relative norm in the same quadratic field used by the unitary model. -/
theorem quadratic_norm (t : Quadratic F p) :
    algebraMap F (Quadratic F p) (Algebra.norm F t) = t * quadraticConj F p t := by
  rw [FiniteField.algebraMap_norm_eq_prod_pow, FiniteField.finrank_extension]
  simp [Finset.prod_range_succ, quadraticConj, FiniteField.Extension.frob_apply]

/-- A norm minus one vector makes the unitary octonion algebra isotropic. -/
theorem exists_norm_minus_one : ∃ t : Quadratic F p, t * quadraticConj F p t = -1 := by
  obtain ⟨t, ht⟩ := FiniteField.norm_surjective F (Quadratic F p) (-1)
  exact ⟨t, (quadratic_norm F p t).symm.trans (by rw [ht, map_neg, map_one])⟩

/-- The elementary nontrivial idempotent provided by a norm minus one vector. -/
def splitIdempotent (t : Quadratic F p) : Octonion F p :=
  ((2 : Quadratic F p)⁻¹, ![(2 : Quadratic F p)⁻¹ * t, 0, 0])

theorem splitIdempotent_mul_self (h2 : (2 : Quadratic F p) ≠ 0)
    (t : Quadratic F p) (ht : t * quadraticConj F p t = -1) :
    octonionMul F p (splitIdempotent F p t) (splitIdempotent F p t) =
      splitIdempotent F p t := by
  apply Prod.ext
  · simp [octonionMul, splitIdempotent, dotProduct, Fin.sum_univ_three, map_ofNat]
    field_simp [h2]
    linear_combination -ht
  · ext i
    fin_cases i <;> simp [octonionMul, splitIdempotent, Matrix.vecHead, Matrix.vecTail, map_ofNat]
    field_simp [h2]
    ring

theorem finrank_octonion : Module.finrank F (Octonion F p) = 8 := by
  simp [Octonion, Module.finrank_prod, Module.finrank_pi_fintype,
    FiniteField.finrank_extension]

omit [Finite F] in
theorem splitIdempotent_ne_zero (h2 : (2 : Quadratic F p) ≠ 0) (t : Quadratic F p) :
    splitIdempotent F p t ≠ 0 := by
  intro h
  exact (inv_ne_zero h2) (congrArg Prod.fst h)

omit [Finite F] in
theorem splitIdempotent_ne_unit (t : Quadratic F p) :
    splitIdempotent F p t ≠ (1, 0) := by
  intro h
  have h2 : (2 : Quadratic F p) = 1 := inv_eq_one.mp (congrArg Prod.fst h)
  have h1 : (1 : Quadratic F p) = 0 := by linear_combination h2
  exact one_ne_zero h1

theorem exists_nontrivial_idempotent (hp : 3 < p) :
    ∃ e : Octonion F p, octonionMul F p e e = e ∧ e ≠ 0 ∧ e ≠ (1, 0) := by
  have h2 : (2 : Quadratic F p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (Quadratic F p) Nat.prime_two (by omega : p ≠ 2)
  obtain ⟨t, ht⟩ := exists_norm_minus_one F p
  exact ⟨splitIdempotent F p t, splitIdempotent_mul_self F p h2 t ht,
    splitIdempotent_ne_zero F p h2 t, splitIdempotent_ne_unit F p t⟩

/-- A nonzero imaginary coordinate in the genuine quadratic extension. -/
theorem exists_trace_zero_generator :
    ∃ d : Quadratic F p, d ≠ 0 ∧ quadraticConj F p d = -d := by
  have hfrob : FiniteField.Extension.frob F p 2 ≠ 1 := by
    intro h
    have hord : orderOf (FiniteField.Extension.frob F p 2) = 2 := by
      let := Fintype.ofFinite F
      rw [FiniteField.Extension.frob,
        FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, FiniteField.finrank_extension]
    rw [h, orderOf_one] at hord
    omega
  have hx : ∃ x : Quadratic F p, quadraticConj F p x ≠ x := by
    by_contra h
    apply hfrob
    ext x
    exact not_ne_iff.mp (not_exists.mp h x)
  obtain ⟨x, hx⟩ := hx
  refine ⟨x - quadraticConj F p x, sub_ne_zero.mpr hx.symm, ?_⟩
  rw [map_sub, conj_conj]
  ring

end
end Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryEmbedding

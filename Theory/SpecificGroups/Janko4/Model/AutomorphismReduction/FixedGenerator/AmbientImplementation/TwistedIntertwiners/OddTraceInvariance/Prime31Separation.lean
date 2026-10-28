module

public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders.Prime31
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!+# Distinct binary traces inside one order-31 subgroup of J₄

The certified order-31 word has binary trace one, whereas its cube has binary
trace zero. Both elements have order 31 and generate the same cyclic subgroup.
Consequently, knowing an element's order, or its cyclic subgroup up to
conjugacy, does not determine its trace in the literal 112-dimensional module.

The two trace computations reuse the packed rows and multiplication proofs in
`Simplicity.PrimeCoverage.WordOrders.Prime31`; only the 112 diagonal entries
are evaluated here. The faithful matrix inclusion transfers the certified word
order to the actual carrier. No group-order, simplicity, irreducibility, or
conjugacy-table assumption is used.

The word and matrix data come from ATLAS `J4G1-f2r112B0`, with source attribution
and bit conventions in `Model.Data` and `Model.Simplicity.Words`. This separates
two actual elements; it does not produce an automorphism interchanging them
and does not refute automorphism invariance of the trace.
-/

namespace Janko4.OuterReduction.FixedGenerator.OddTrace

open Janko4.Simplicity.WordOrderCertificates

/-- The literal word used by the existing order-31 certificate. -/
@[expose] public def traceWitness31 : Model :=
  (a * b * a * b * b) * (b * ((a * b) * (a * b * a * b * b)))

private theorem toMatrix_traceWitness31 : toMatrix traceWitness31 = matrixWord31 := by
  simp only [traceWitness31, map_mul, toMatrix_a, toMatrix_b, matrixWord31]

/-- The word-order certificate concerns this element of the actual carrier. -/
public theorem orderOf_traceWitness31 : orderOf traceWitness31 = 31 := by
  rw [← orderOf_injective toMatrix toMatrix_injective, toMatrix_traceWitness31]
  simpa only [pow_one] using orderOf_matrixWord31_representative

/-- Cubing preserves the order of this element. -/
public theorem orderOf_traceWitness31_cube : orderOf (traceWitness31 ^ 3) = 31 := by
  rw [orderOf_pow, orderOf_traceWitness31]
  decide

/-- The two elements generate exactly the same subgroup of the matrix carrier. -/
public theorem zpowers_traceWitness31_cube :
    Subgroup.zpowers (traceWitness31 ^ 3) = Subgroup.zpowers traceWitness31 := by
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers traceWitness31 3)
  · apply Subgroup.zpowers_le.mpr
    rw [mem_zpowers_pow_iff, orderOf_traceWitness31]
    decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- The trace of the certified order-31 word is one. -/
public theorem trace_traceWitness31 : Matrix.trace (toMatrix traceWitness31) = 1 := by
  rw [toMatrix_traceWitness31, ← pow_one matrixWord31, ← decode_p31e1]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- The trace of its cube is zero, using the already checked cube matrix. -/
public theorem trace_traceWitness31_cube :
    Matrix.trace (toMatrix (traceWitness31 ^ 3)) = 0 := by
  rw [map_pow, toMatrix_traceWitness31, ← decode_p31e3]
  decide +kernel

/-- These generators of the same cyclic subgroup lie in different conjugacy classes. -/
public theorem not_isConj_traceWitness31_cube :
    ¬ IsConj traceWitness31 (traceWitness31 ^ 3) := by
  intro hc
  obtain ⟨c, heq⟩ := isConj_iff.mp hc
  have h := congrArg (fun g => Matrix.trace (toMatrix g)) heq
  rw [map_mul, map_mul, Matrix.trace_mul_cycle, ← map_mul, inv_mul_cancel,
    map_one, one_mul, trace_traceWitness31, trace_traceWitness31_cube] at h
  exact one_ne_zero h

/-- Odd-order binary trace cannot be computed from the element order alone. -/
public theorem trace_not_determined_by_odd_order :
    ¬ ∃ f : ℕ → ZMod 2, ∀ g : Model, Odd (orderOf g) →
      Matrix.trace (toMatrix g) = f (orderOf g) := by
  rintro ⟨f, hf⟩
  have h₁ := hf traceWitness31 (by rw [orderOf_traceWitness31]; decide)
  have h₂ := hf (traceWitness31 ^ 3) (by rw [orderOf_traceWitness31_cube]; decide)
  rw [trace_traceWitness31, orderOf_traceWitness31] at h₁
  rw [trace_traceWitness31_cube, orderOf_traceWitness31_cube] at h₂
  exact one_ne_zero (h₁.trans h₂.symm)

end Janko4.OuterReduction.FixedGenerator.OddTrace

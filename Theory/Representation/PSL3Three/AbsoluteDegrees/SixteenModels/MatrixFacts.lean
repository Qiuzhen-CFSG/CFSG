module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Data
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Native generation and the marked degree-sixteen trace

The ATLAS standard generators generate the native SL₃(3): short matrix
identities recover the coordinate cycle and elementary transvection of
`PSL3Three.Generators`. On the explicit degree-sixteen matrices their product
has trace `t³+t+1` whenever `t⁴=t+1` in characteristic two.

These finite checks are used by the native action construction and by the
inequivalence argument. They do not assert the degree-sixteen group law or
density. The numerical data and source attribution are in `Data`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels
variable {F : Type*} [Field F] [CharP F 2]

theorem trace_matrix_product (t : F) (ht : t ^ 4 = t + 1) :
    (matrixA t * matrixB t).trace = traceParameter t := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ,
    matrixA, matrixB, codesA, codesB, Matrix.map_apply, coefficient, traceParameter]
  ring_nf
  have h4 : (4 : F) = 0 := (CharP.cast_eq_zero_iff F 2 4).mpr (by decide)
  have h5 : (5 : F) = 1 := by linear_combination 2 * (CharTwo.two_eq_zero (R := F))
  have h7 : (7 : F) = 1 := by linear_combination 3 * (CharTwo.two_eq_zero (R := F))
  simp only [h4, h5, h7, CharTwo.two_eq_zero, mul_zero, mul_one, zero_add, add_zero, ht]
  ring

theorem native_generators (H : Subgroup Matrix.PSL3Three.SL) (ha : nativeA ∈ H) (hb : nativeB ∈ H) :
    H = ⊤ := by
  let u : Matrix.PSL3Three.SL := ⟨!![2, 2, 0; 1, 0, 2; 1, 0, 0], by decide⟩
  let v : Matrix.PSL3Three.SL := ⟨!![1, 0, 2; 1, 0, 0; 2, 2, 0], by decide⟩
  let w : Matrix.PSL3Three.SL := ⟨!![2, 2, 2; 0, 2, 0; 0, 1, 1], by decide⟩
  have hu : nativeB * nativeA = u := by apply Subtype.ext; decide
  have hv : nativeB * nativeB * nativeA = v := by apply Subtype.ext; decide
  have hw : v * u * u * v = w := by apply Subtype.ext; decide
  have huw : u ∈ H := hu ▸ H.mul_mem hb ha
  have hvw : v ∈ H := hv ▸ H.mul_mem (H.mul_mem hb hb) ha
  have hww : w ∈ H := hw ▸ H.mul_mem (H.mul_mem (H.mul_mem hvw huw) huw) hvw
  have h0 : nativeB * nativeB = Matrix.PSL3Three.ambientGenerators 0 := by decide
  have h1 : w * w = Matrix.PSL3Three.ambientGenerators 1 := by decide
  have h0m : Matrix.PSL3Three.ambientGenerators 0 ∈ H := h0 ▸ H.mul_mem hb hb
  have h1m : Matrix.PSL3Three.ambientGenerators 1 ∈ H := h1 ▸ H.mul_mem hww hww
  apply Matrix.PSL3Three.eq_top_of_ambientGenerators_mem
  intro i
  fin_cases i
  · exact h0m
  · exact h1m
  · have h := H.inv_mem h0m
    rwa [← Matrix.PSL3Three.ambientGenerators_inverse 0] at h
  · have h := H.inv_mem h1m
    rwa [← Matrix.PSL3Three.ambientGenerators_inverse 1] at h


end Representation.PSL3Three.AbsoluteDegrees.SixteenModels

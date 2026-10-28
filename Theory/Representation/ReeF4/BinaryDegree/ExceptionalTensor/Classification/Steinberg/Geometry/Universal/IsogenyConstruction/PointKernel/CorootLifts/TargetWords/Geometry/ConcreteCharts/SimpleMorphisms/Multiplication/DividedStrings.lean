module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms.Polynomial

/-!
# Multiplication on divided root strings

The explicit integral divided-power coefficients multiply in the same order as
2-by-2 matrices. Root strings in a reduced crystallographic root system have
degree at most three; the small polynomial identities below cover precisely
those degrees, over any commutative ring and without dividing by factorials.
The separate coefficient lemmas keep normalization and kernel checking bounded.

Source: the integral root-string construction behind GLS3, Remark 1.12.10.
-/

@[expose] public section
open scoped BigOperators
open Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
private lemma certificate_0_0_0 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 0 0 0 (A * B) =
      ∑ t ∈ Finset.range 1, dividedStringEntry 0 t 0 A * dividedStringEntry 0 0 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
private lemma certificate_1_0_0 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 1 0 0 (A * B) =
      ∑ t ∈ Finset.range 2, dividedStringEntry 1 t 0 A * dividedStringEntry 1 0 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_1_0_1 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 1 0 1 (A * B) =
      ∑ t ∈ Finset.range 2, dividedStringEntry 1 t 1 A * dividedStringEntry 1 0 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_1_1_0 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 1 1 0 (A * B) =
      ∑ t ∈ Finset.range 2, dividedStringEntry 1 t 0 A * dividedStringEntry 1 1 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_1_1_1 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 1 1 1 (A * B) =
      ∑ t ∈ Finset.range 2, dividedStringEntry 1 t 1 A * dividedStringEntry 1 1 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_2_0_0 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 2 0 0 (A * B) =
      ∑ t ∈ Finset.range 3, dividedStringEntry 2 t 0 A * dividedStringEntry 2 0 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_2_0_1 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 2 0 1 (A * B) =
      ∑ t ∈ Finset.range 3, dividedStringEntry 2 t 1 A * dividedStringEntry 2 0 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_2_0_2 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 2 0 2 (A * B) =
      ∑ t ∈ Finset.range 3, dividedStringEntry 2 t 2 A * dividedStringEntry 2 0 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_2_1_0 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 2 1 0 (A * B) =
      ∑ t ∈ Finset.range 3, dividedStringEntry 2 t 0 A * dividedStringEntry 2 1 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_2_1_1 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 2 1 1 (A * B) =
      ∑ t ∈ Finset.range 3, dividedStringEntry 2 t 1 A * dividedStringEntry 2 1 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_2_1_2 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 2 1 2 (A * B) =
      ∑ t ∈ Finset.range 3, dividedStringEntry 2 t 2 A * dividedStringEntry 2 1 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_2_2_0 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 2 2 0 (A * B) =
      ∑ t ∈ Finset.range 3, dividedStringEntry 2 t 0 A * dividedStringEntry 2 2 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_2_2_1 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 2 2 1 (A * B) =
      ∑ t ∈ Finset.range 3, dividedStringEntry 2 t 1 A * dividedStringEntry 2 2 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_2_2_2 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 2 2 2 (A * B) =
      ∑ t ∈ Finset.range 3, dividedStringEntry 2 t 2 A * dividedStringEntry 2 2 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_0_0 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 0 0 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 0 A * dividedStringEntry 3 0 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_0_1 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 0 1 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 1 A * dividedStringEntry 3 0 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_0_2 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 0 2 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 2 A * dividedStringEntry 3 0 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_0_3 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 0 3 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 3 A * dividedStringEntry 3 0 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_1_0 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 1 0 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 0 A * dividedStringEntry 3 1 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_1_1 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 1 1 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 1 A * dividedStringEntry 3 1 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_1_2 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 1 2 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 2 A * dividedStringEntry 3 1 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_1_3 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 1 3 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 3 A * dividedStringEntry 3 1 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_2_0 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 2 0 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 0 A * dividedStringEntry 3 2 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_2_1 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 2 1 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 1 A * dividedStringEntry 3 2 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_2_2 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 2 2 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 2 A * dividedStringEntry 3 2 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_2_3 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 2 3 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 3 A * dividedStringEntry 3 2 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_3_0 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 3 0 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 0 A * dividedStringEntry 3 3 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_3_1 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 3 1 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 1 A * dividedStringEntry 3 3 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_3_2 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 3 2 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 2 A * dividedStringEntry 3 3 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma certificate_3_3_3 {k : Type*} [CommRing k] (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry 3 3 3 (A * B) =
      ∑ t ∈ Finset.range 4, dividedStringEntry 3 t 3 A * dividedStringEntry 3 3 t B := by
  norm_num [dividedStringEntry, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring

namespace Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
/-- Convolution of the integral divided-string coefficients in every root-string degree. -/
lemma dividedStringEntry_mul_le_three {k : Type*} [CommRing k]
    (n q r : ℕ) (hn : n ≤ 3) (hq : q ≤ n) (hr : r ≤ n)
    (A B : Matrix (Fin 2) (Fin 2) k) :
    dividedStringEntry n q r (A * B) =
      ∑ t ∈ Finset.range (n + 1), dividedStringEntry n t r A * dividedStringEntry n q t B := by
  interval_cases n <;> interval_cases q <;> interval_cases r
  · exact certificate_0_0_0 A B
  · exact certificate_1_0_0 A B
  · exact certificate_1_0_1 A B
  · exact certificate_1_1_0 A B
  · exact certificate_1_1_1 A B
  · exact certificate_2_0_0 A B
  · exact certificate_2_0_1 A B
  · exact certificate_2_0_2 A B
  · exact certificate_2_1_0 A B
  · exact certificate_2_1_1 A B
  · exact certificate_2_1_2 A B
  · exact certificate_2_2_0 A B
  · exact certificate_2_2_1 A B
  · exact certificate_2_2_2 A B
  · exact certificate_3_0_0 A B
  · exact certificate_3_0_1 A B
  · exact certificate_3_0_2 A B
  · exact certificate_3_0_3 A B
  · exact certificate_3_1_0 A B
  · exact certificate_3_1_1 A B
  · exact certificate_3_1_2 A B
  · exact certificate_3_1_3 A B
  · exact certificate_3_2_0 A B
  · exact certificate_3_2_1 A B
  · exact certificate_3_2_2 A B
  · exact certificate_3_2_3 A B
  · exact certificate_3_3_0 A B
  · exact certificate_3_3_1 A B
  · exact certificate_3_3_2 A B
  · exact certificate_3_3_3 A B
end Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts

module

public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic

/-!
# Exponent of noncommutative-subgroup centralizers in PGL₂

Over any field, every element centralizing a noncommutative subgroup of
PGL₂ has square one. Lift the element to a two-by-two matrix. If its trace
vanishes, its square is scalar. Otherwise the trace removes the scalar
ambiguity in projective commutation, and the existing GL₂ centralizer
theorem makes the lift itself scalar. An actual model transports the bound.

This elementary matrix proof supplies the full-automorphism centralizer
calculation in Aschbacher–Smith, proof of 2.5.21, printed p.567. It covers
subgroups meeting the outer coset as well as subgroups of PSL₂.
-/

public section

open Matrix Subgroup
open scoped MatrixGroups
namespace Theory.PGL2
variable {F : Type*} [Field F]

private theorem square_scalar_of_trace_zero (A : GL (Fin 2) F)
    (ht : A.val.trace = 0) : A * A = GeneralLinearGroup.scalar (Fin 2) (-A.det) := by
  rw [Matrix.trace_fin_two] at ht
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_neg,
    GeneralLinearGroup.val_det_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.scalar_apply, Matrix.det_fin_two, Fin.isValue]
  · linear_combination A.val 0 0 * ht
  · linear_combination A.val 0 1 * ht
  · linear_combination A.val 1 0 * ht
  · linear_combination A.val 1 1 * ht

private theorem commute_lifts_of_trace_ne_zero (A B : GL (Fin 2) F)
    (ht : A.val.trace ≠ 0) (hc : Commute (ProjGenLinGroup.mk A) (ProjGenLinGroup.mk B)) :
    Commute A B := by
  have hp : ProjGenLinGroup.mk (B * A * B⁻¹) = ProjGenLinGroup.mk A := by
    simp only [map_mul, map_inv]
    rw [hc.eq.symm]
    group
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have hs (C : GL (Fin 2) F) :
      (C * GeneralLinearGroup.scalar (Fin 2) u).val.trace = (u : F) * C.val.trace := by
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      GeneralLinearGroup.scalar, Matrix.scalar_apply]
    ring
  have htrace := congrArg (fun C : GL (Fin 2) F => C.val.trace) hu
  rw [hs] at htrace
  change (u : F) * (B.val * A.val * (B⁻¹).val).trace = A.val.trace at htrace
  rw [Matrix.trace_units_conj] at htrace
  have hu1 : u = 1 := Units.ext ((mul_right_cancel₀ ht) (htrace.trans (one_mul _).symm))
  have hBA : B * A * B⁻¹ = A := by simpa [hu1] using hu
  have hc' := congrArg (fun C : GL (Fin 2) F => C * B) hBA
  exact (show B * A = A * B by simpa only [mul_assoc, inv_mul_cancel, mul_one] using hc').symm

/-- Any element centralizing a noncommutative PGL₂ subgroup has square one.
The subgroup may have elements outside PSL₂. -/
theorem centralizer_square_eq_one (D : Subgroup (PGL(2, F)))
    (hD : ¬ IsMulCommutative D) {a : PGL(2, F)} (ha : a ∈ centralizer (D : Set _)) :
    a ^ 2 = 1 := by
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective a
  by_cases ht : A.val.trace = 0
  · rw [← map_pow, pow_two, square_scalar_of_trace_zero A ht, ProjGenLinGroup.mk_scalar]
  let E := D.comap (ProjGenLinGroup.mk : GL (Fin 2) F →* PGL(2, F))
  have hE : ¬ IsMulCommutative E := by
    intro hc
    apply hD
    apply IsMulCommutative.of_comm
    intro d e
    obtain ⟨B, hB⟩ := ProjGenLinGroup.mk_surjective d.val
    obtain ⟨C, hC⟩ := ProjGenLinGroup.mk_surjective e.val
    have hBE : B ∈ E := by change ProjGenLinGroup.mk B ∈ D; rw [hB]; exact d.property
    have hCE : C ∈ E := by change ProjGenLinGroup.mk C ∈ D; rw [hC]; exact e.property
    have hh := congrArg (fun y : E => ProjGenLinGroup.mk y.val)
      (hc.is_comm.comm ⟨B, hBE⟩ ⟨C, hCE⟩)
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, map_mul, hB, hC] using hh
  have hA : A ∈ centralizer (E : Set _) := by
    intro B hB
    exact (commute_lifts_of_trace_ne_zero A B ht (ha _ hB).symm).eq.symm
  obtain ⟨u, hu⟩ := GeneralLinearGroup.centralizer_le_scalar_of_noncommutative E hE hA
  rw [← hu, ProjGenLinGroup.mk_scalar, one_pow]

/-- The square bound transports along an actual PGL₂ model. -/
theorem centralizer_square_eq_one_of_model {X : Type*} [Group X]
    (e : X ≃* PGL(2, F)) (D : Subgroup X) (hD : ¬ IsMulCommutative D)
    {a : X} (ha : a ∈ centralizer (D : Set X)) : a ^ 2 = 1 := by
  let E := D.map e.toMonoidHom
  have hE : ¬ IsMulCommutative E := by
    intro hc
    apply hD
    apply IsMulCommutative.of_comm
    intro b c
    apply Subtype.ext
    apply e.injective
    have hh := congrArg (fun y : E => y.val)
      (hc.is_comm.comm ⟨e b, mem_map_of_mem _ b.property⟩
        ⟨e c, mem_map_of_mem _ c.property⟩)
    simpa only [Subgroup.coe_mul, map_mul] using hh
  have haE : e a ∈ centralizer (E : Set _) := by
    rintro _ ⟨b, hb, rfl⟩
    change e b * e a = e a * e b
    simpa only [map_mul] using congrArg e (ha b hb)
  apply e.injective
  rw [map_pow, map_one]
  exact centralizer_square_eq_one E hE haE

end Theory.PGL2

end

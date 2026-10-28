module

public import Theory.LinearAlgebra.MatrixTwoCentralizerDeterminant
public import Theory.LinearAlgebra.MatrixTwoCyclicIntertwiner
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.CharP.Reduced

/-!
# Involution fusion in finite PSL₂

A lift of a nonidentity projective involution is nonscalar and its square
is scalar. The matrix entries then force its trace to be zero. Equal trace
and determinant give a GL₂ intertwiner. In odd characteristic the centralizer
has surjective determinant; in characteristic two every field element has a
square root, so a scalar matrix corrects the determinant instead. The resulting
SL₂ conjugacy descends through the actual quotient by the center.

This supplies both linear families in the simple case of Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 16.2.6, printed p.1174
(combined manuscript of 1 March 2004). The argument works over every finite
field, independently of the source's parameter and simplicity restrictions.
-/

open Matrix
namespace Theory.PSL2
variable {K : Type*} [Field K]

private theorem nonscalar_of_projective_ne_one (A : SpecialLinearGroup (Fin 2) K)
    (hA : QuotientGroup.mk A ≠ (1 : ProjectiveSpecialLinearGroup (Fin 2) K)) :
    ¬ ∃ r : K, A.val = r • 1 := by
  rintro ⟨r, hr⟩
  apply hA
  apply (QuotientGroup.eq_one_iff A).mpr
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨r, ?_, ?_⟩
  · have hd := A.property
    rw [hr, det_smul, det_one, mul_one, Fintype.card_fin] at hd
    exact hd
  · simpa [smul_one_eq_diagonal] using hr.symm

private theorem trace_zero_of_projective_involution (A : SpecialLinearGroup (Fin 2) K)
    (hA : ¬ ∃ r : K, A.val = r • 1)
    (hsq : QuotientGroup.mk A ^ 2 = (1 : ProjectiveSpecialLinearGroup (Fin 2) K)) :
    trace A.val = 0 := by
  have hc : A ^ 2 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) K))) (A ^ 2) = 1
    rw [map_pow]
    exact hsq
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have he : A.val * A.val = r • (1 : Matrix (Fin 2) (Fin 2) K) := by
    simpa only [pow_two, Matrix.SpecialLinearGroup.coe_mul, scalar_apply, smul_one_eq_diagonal] using hr.symm
  by_contra ht
  apply hA
  refine ⟨A.val 0 0, ?_⟩
  have hb := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) he
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) he
  have hd := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0 - M 1 1) he
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hb hc hd
  have hb0 : A.val 0 1 = 0 := (mul_eq_zero.mp (show A.val 0 1 * trace A.val = 0 by
    rw [trace_fin_two]; linear_combination hb)).resolve_right ht
  have hc0 : A.val 1 0 = 0 := (mul_eq_zero.mp (show A.val 1 0 * trace A.val = 0 by
    rw [trace_fin_two]; linear_combination hc)).resolve_right ht
  have hd0 : A.val 0 0 = A.val 1 1 := sub_eq_zero.mp
    ((mul_eq_zero.mp (show (A.val 0 0 - A.val 1 1) * trace A.val = 0 by
      rw [trace_fin_two]; linear_combination hd)).resolve_right ht)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb0, hc0, hd0]

private theorem trace_zero_isConj [Finite K] (A B : SpecialLinearGroup (Fin 2) K)
    (hA : ¬ ∃ r : K, A.val = r • 1) (hB : ¬ ∃ r : K, B.val = r • 1)
    (htA : trace A.val = 0) (htB : trace B.val = 0) : IsConj A B := by
  obtain ⟨D, hD, hAD⟩ := Matrix.exists_intertwiner_of_trace_eq_det_eq
    A.val B.val hA hB (htA.trans htB.symm) (A.property.trans B.property.symm)
  have hC : ∃ C : Matrix (Fin 2) (Fin 2) K,
      C * B.val = B.val * C ∧ det C = (det D)⁻¹ := by
    by_cases htwo : (2 : K) = 0
    · have : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr htwo
      obtain ⟨s, hs⟩ := (Finite.surjective_of_injective (frobenius_inj K 2)) (det D)⁻¹
      refine ⟨s • 1, ?_, ?_⟩
      · simp
      · simpa [frobenius_def] using hs
    · exact Matrix.exists_commuting_det_of_trace_sq_ne_four_det B.val
        (by
          rw [htB, B.property]
          have hfour : (4 : K) ≠ 0 := by
            convert mul_ne_zero htwo htwo using 1
            norm_num
          simpa only [zero_pow (by decide : 2 ≠ 0), mul_one, ne_eq, eq_comm] using hfour) (det D)⁻¹
  obtain ⟨C, hCB, hC⟩ := hC
  let g : SpecialLinearGroup (Fin 2) K :=
    ⟨D * C, by rw [det_mul, hC]; exact mul_inv_cancel₀ hD⟩
  have hAg : A * g = g * B := by
    apply Subtype.ext
    change A.val * (D * C) = (D * C) * B.val
    rw [← Matrix.mul_assoc, hAD, Matrix.mul_assoc, ← hCB, ← Matrix.mul_assoc]
  exact (isConj_iff.mpr ⟨g, mul_inv_eq_iff_eq_mul.mpr hAg.symm⟩).symm

/-- All involutions of the actual central quotient PSL₂ over a finite field are conjugate. -/
public theorem involutions_isConj [Finite K]
    (a b : ProjectiveSpecialLinearGroup (Fin 2) K)
    (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin 2) K)) a
  obtain ⟨B, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin 2) K)) b
  have ha' := (orderOf_eq_prime_iff (p := 2)).mp ha
  have hb' := (orderOf_eq_prime_iff (p := 2)).mp hb
  have hA := nonscalar_of_projective_ne_one A ha'.2
  have hB := nonscalar_of_projective_ne_one B hb'.2
  exact (QuotientGroup.mk' _).map_isConj (trace_zero_isConj A B hA hB
    (trace_zero_of_projective_involution A hA ha'.1)
    (trace_zero_of_projective_involution B hB hb'.1))
end Theory.PSL2

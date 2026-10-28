module

public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.FieldAction
/-!
# Determinant-one descent for an involutory SL₂ cocycle

For A σ(A) = 1 set B = tI + σ(t)A. Then A σ(B) = B. If A has nonzero
trace, t = 1 makes B invertible. Otherwise any nonfixed t works: its determinant
is (t + σ(t))². The determinant of B is fixed by σ. In a finite field of
characteristic two it has a unique square root r, also fixed by σ. Therefore
C = r⁻¹B has determinant one and A = C σ(C)⁻¹.

This is the explicit two-dimensional Hilbert–90 calculation needed in the
binary linear case of GLS, Volume 4, Chapter 4, Lemma 3.4(c). It does not assume
simplicity or exclude the square-root field GF(2).
Adapted from the corresponding `BenderSuzuki.ZD.Linear` module; the
original campaign proofs are preserved. This extension has only Theory and
Mathlib imports and also supplies GLS, Volume 2, Theorem 26.24.
-/

namespace Theory.PSL2
open Matrix
variable {K : Type*} [Field K]

private theorem det_twisted_sum (A : SpecialLinearGroup (Fin 2) K) (t u : K) :
    (t • (1 : Matrix (Fin 2) (Fin 2) K) + u • A.val).det =
      t ^ 2 + t * u * (A 0 0 + A 1 1) + u ^ 2 := by
  have hd := A.property
  rw [det_fin_two] at hd
  simp [det_fin_two, Matrix.add_apply, Matrix.smul_apply]
  linear_combination u ^ 2 * hd

variable [CharP K 2]

private theorem exists_twisted_sum_det_ne_zero (σ : K ≃+* K)
    (hne : σ ≠ RingEquiv.refl K) (A : SpecialLinearGroup (Fin 2) K) :
    ∃ t : K, (t • (1 : Matrix (Fin 2) (Fin 2) K) + σ t • A.val).det ≠ 0 := by
  by_cases ht : A 0 0 + A 1 1 = 0
  · obtain ⟨t, htσ⟩ : ∃ t, σ t ≠ t := by
      by_contra h
      apply hne
      ext t
      exact not_not.mp (not_exists.mp h t)
    refine ⟨t, ?_⟩
    rw [det_twisted_sum, ht, mul_zero, add_zero]
    have hsq : t ^ 2 + (σ t) ^ 2 = (t + σ t) ^ 2 := by
      rw [add_sq, (CharTwo.two_eq_zero : (2 : K) = 0), zero_mul, zero_mul, add_zero]
    rw [hsq]
    apply pow_ne_zero _
    intro h
    apply htσ
    calc
      σ t = t + (t + σ t) := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      _ = t := by rw [h, add_zero]
  · refine ⟨1, ?_⟩
    rw [det_twisted_sum, map_one, one_pow, mul_one, one_mul]
    simpa only [add_right_comm, CharTwo.add_self_eq_zero, zero_add] using ht

variable [Finite K]

public theorem involutory_sl2_cocycle_trivial
    (σ : K ≃+* K) (hs : Function.Involutive σ) (hne : σ ≠ RingEquiv.refl K)
    (A : SpecialLinearGroup (Fin 2) K) (hA : A * sl2FieldAut σ A = 1) :
    ∃ C : SpecialLinearGroup (Fin 2) K, A = C * (sl2FieldAut σ C)⁻¹ := by
  obtain ⟨t, ht⟩ := exists_twisted_sum_det_ne_zero σ hne A
  let B : Matrix (Fin 2) (Fin 2) K := t • 1 + σ t • A.val
  have hdet : B.det ≠ 0 := ht
  have hAm : A.val * A.val.map σ = 1 := by
    exact congrArg (fun X : SpecialLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) hA
  have hmap : B.map σ = σ t • 1 + t • A.val.map σ := by
    ext i j
    simp only [B, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, hs t]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hB : A.val * B.map σ = B := by
    rw [hmap, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hAm,
      Matrix.mul_one]
    exact add_comm _ _
  have hdσ : σ B.det = B.det := by
    have h := congrArg Matrix.det hB
    rw [Matrix.det_mul, A.property, one_mul] at h
    exact (σ.toRingHom.map_det B).trans h
  obtain ⟨r, hr⟩ := (Finite.surjective_of_injective (frobenius_inj K 2)) B.det
  change r ^ 2 = B.det at hr
  have hr0 : r ≠ 0 := by
    intro hz
    apply hdet
    rw [← hr, hz, zero_pow (by decide : 2 ≠ 0)]
  have hrs : σ r = r := by
    apply frobenius_inj K 2
    change (σ r) ^ 2 = r ^ 2
    rw [← map_pow, hr, hdσ]
  let C : SpecialLinearGroup (Fin 2) K := ⟨r⁻¹ • B, by
    rw [Matrix.det_smul, Fintype.card_fin, ← hr, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hr0)]⟩
  refine ⟨C, (eq_mul_inv_iff_mul_eq).mpr ?_⟩
  apply Subtype.ext
  change A.val * (r⁻¹ • B).map σ = r⁻¹ • B
  have hm : (r⁻¹ • B).map σ = r⁻¹ • B.map σ := by
    ext i j
    simp [Matrix.map_apply, hrs]
  rw [hm, Matrix.mul_smul, hB]
end Theory.PSL2

module

public import Theory.Representation.OrthogonalFourMinusFirstCohomology.Model
public import Mathlib.FieldTheory.Finite.GaloisField
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Geometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Ambient cohomology for the quadratic twisted tensor module

Over a finite field of characteristic two, the full matrix space with action
`X ↦ A X σ(A)ᵀ` has zero first cohomology whenever `σ` is nonidentity.
The two transvection subgroups also show directly that its fixed space is zero.
The final theorems specialize both statements to the quadratic Frobenius on
`GF(2^(2n))`, for every positive `n`.

For the cocycle calculation, average over the odd-order diagonal torus to
normalize its values to zero. The upper involutions and their commutation
relations force the off-diagonal entries of an upper value to be `βt, βσ(t)`.
After removing the quadratic term `βtσ(t)`, its remaining entry is additive.
Torus covariance and a nonfixed field element make that additive term zero.
Subtracting the principal cocycle of `βE₁₁` therefore kills the upper values
while preserving torus normalization. The Weyl value is then scalar; the
principal cocycle of a multiple of `E₀₀` removes it without changing upper
values. Weyl conjugation and transvection generation finish the proof.
The torus-fixed corrections are retained, including over the field of order four.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma I.1.6(3), printed p.408 (PDF p.419), citing
Jones--Parshall [JP76]. This is the ambient twisted-tensor calculation;
`principal_surjective_of_tensor` supplies the separate Hermitian descent.
-/

open Matrix Matrix.SpecialLinearGroup
open Representation Representation.OneCohomology

namespace Representation.OrthogonalFourMinus

variable {F : Type*} [Field F] [CharP F 2]

private abbrev upper (t : F) : SpecialLinearGroup (Fin 2) F :=
  transvection zero_ne_one t

private abbrev lower (t : F) : SpecialLinearGroup (Fin 2) F :=
  transvection one_ne_zero t

omit [CharP F 2] in
private lemma upper_apply (σ : F ≃+* F) (t : F) (X : Mat F) :
    tensorAction σ (upper t) X =
      !![(X 0 0) + t * (X 1 0) + σ t * (X 0 1) + t * σ t * (X 1 1),
         (X 0 1) + t * (X 1 1);
         (X 1 0) + σ t * (X 1 1), (X 1 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorAction_apply, upper, transvection_coe, adjoint, Matrix.mul_apply,
      Fin.sum_univ_two, map_add]
  <;> ring

omit [CharP F 2] in
private lemma lower_apply (σ : F ≃+* F) (t : F) (X : Mat F) :
    tensorAction σ (lower t) X =
      !![(X 0 0), (σ t) * (X 0 0) + (X 0 1);
         (t * (X 0 0) + X 1 0),
         t * σ t * (X 0 0) + σ t * (X 1 0) + t * (X 0 1) + (X 1 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorAction_apply, lower, transvection_coe, adjoint, Matrix.mul_apply,
      Fin.sum_univ_two, map_add]
  <;> ring

private lemma fixed_zero (σ : F ≃+* F) (hσ : ∃ t : F, σ t ≠ t) :
    OneCohomology.fixed (tensorAction σ) = ⊥ := by
  apply bot_unique
  intro X hX
  change X = 0
  obtain ⟨t, ht⟩ := hσ
  have ht0 : t ≠ 0 := by
    intro ht0
    apply ht
    simp [ht0]
  have hσt0 : σ t ≠ 0 := (map_ne_zero σ).mpr ht0
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hu := hX (upper t)
  have hl := hX (lower t)
  rw [upper_apply] at hu
  rw [lower_apply] at hl
  have h00 : X 0 0 = 0 := by
    have h := congrArg (fun Y : Mat F => Y 0 1) hl
    simpa [map_one, ht0, hσt0] using h
  have h11 : X 1 1 = 0 := by
    have h := congrArg (fun Y : Mat F => Y 1 0) hu
    simpa [map_one, ht0, hσt0] using h
  have hrel₁ := congrArg (fun Y : Mat F => Y 0 0) hu
  have hrel₂ := congrArg (fun Y : Mat F => Y 1 1) hl
  simp [h00, h11] at hrel₁ hrel₂
  have h01 : X 0 1 = 0 := by
    have hsq : σ t ^ 2 + t ^ 2 ≠ 0 := by
      intro h
      apply ht
      apply CharTwo.sq_injective
      calc
        σ t ^ 2 = σ t ^ 2 + (t ^ 2 + t ^ 2) := by
          rw [CharTwo.add_self_eq_zero, add_zero]
        _ = (σ t ^ 2 + t ^ 2) + t ^ 2 := by ac_rfl
        _ = t ^ 2 := by rw [h]; simp
    have hz : (σ t ^ 2 + t ^ 2) * X 0 1 = 0 := by
      have h₁ : σ t * t * X 1 0 + σ t ^ 2 * X 0 1 = 0 := by
        linear_combination σ t * hrel₁
      have h₂ : t * σ t * X 1 0 + t ^ 2 * X 0 1 = 0 := by
        linear_combination t * hrel₂
      calc
        (σ t ^ 2 + t ^ 2) * X 0 1 =
            (σ t * t * X 1 0 + σ t ^ 2 * X 0 1) +
              (t * σ t * X 1 0 + t ^ 2 * X 0 1) := by
                ring_nf
                simp [htwo]
        _ = 0 := by rw [h₁, h₂, add_zero]
    exact (mul_eq_zero.mp hz).resolve_left hsq
  have h10 : X 1 0 = 0 := by
    have h := hrel₁
    rw [h01] at h
    simpa using (mul_eq_zero.mp (by simpa using h)).resolve_left ht0
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

public theorem tensorAction_fixed_eq_bot (σ : F ≃+* F) (hσ : ∃ t : F, σ t ≠ t) :
    OneCohomology.fixed (tensorAction σ) = ⊥ :=
  fixed_zero σ hσ

private noncomputable abbrev torus (a : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  diag2 a a.ne_zero

omit [CharP F 2] in
private lemma torus_mul (a b : Fˣ) : torus (a * b) = torus a * torus b := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torus, diag2_coe', coe_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

omit [CharP F 2] in
private lemma torus_apply (σ : F ≃+* F) (a : Fˣ) (X : Mat F) :
    tensorAction σ (torus a) X =
      !![(a : F) * σ a * X 0 0, (a : F) * (σ a)⁻¹ * X 0 1;
         (a : F)⁻¹ * σ a * X 1 0, (a : F)⁻¹ * (σ a)⁻¹ * X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorAction_apply, torus, diag2_coe', adjoint, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring

private def swap : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by simp [det_fin_two, CharTwo.neg_eq]⟩

private lemma swap_apply (σ : F ≃+* F) (X : Mat F) :
    tensorAction σ swap X = !![X 1 1, X 1 0; X 0 1, X 0 0] := by
  rw [tensorAction_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap, adjoint, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

private lemma swap_square : (swap : SpecialLinearGroup (Fin 2) F) * swap = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [coe_mul]
  all_goals simp [swap, Matrix.mul_apply, Fin.sum_univ_two]

private lemma torus_swap (a : Fˣ) : torus a * swap = swap * torus a⁻¹ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [coe_mul]
  all_goals simp [torus, diag2_coe', swap, Matrix.mul_apply, Fin.sum_univ_two]

omit [CharP F 2] in
private lemma torus_upper (a : Fˣ) (t : F) :
    torus a * upper t = upper ((a : F)^2 * t) * torus a := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_mul, torus, diag2_coe', upper, transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_two, pow_two, mul_assoc, a.ne_zero, mul_comm]

private lemma swap_upper (t : F) : swap * upper t = lower t * (swap : SpecialLinearGroup (Fin 2) F) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [coe_mul]
  all_goals simp [swap, upper, lower, transvection_coe, Matrix.mul_apply, Fin.sum_univ_two]

private lemma upper_square (t : F) : upper t * upper t = 1 := by
  rw [← transvection_add, CharTwo.add_self_eq_zero, transvection_coeff_zero]

omit [CharP F 2] in
private lemma cocycle_one (σ : F ≃+* F) (f : cocycles (tensorAction σ)) : f.val 1 = 0 := by
  have h := f.property 1 1
  simpa using h.symm

omit [CharP F 2] in
private lemma cocycle_mul (σ : F ≃+* F) (f : cocycles (tensorAction σ))
    (g h : SpecialLinearGroup (Fin 2) F) :
    f.val (g * h) = tensorAction σ g (f.val h) + f.val g := f.property g h

private lemma exists_torus_normalized [Finite F] (σ : F ≃+* F)
    (f : cocycles (tensorAction σ)) :
    ∃ v : Mat F, ∀ a : Fˣ, (f - principal (tensorAction σ) v).val (torus a) = 0 := by
  classical
  let := Fintype.ofFinite F
  have hcard : (Fintype.card Fˣ : F) = 1 := by
    rw [CharTwo.natCast_eq_mod, Fintype.card_units]
    have he := FiniteField.even_card_of_char_two (F := F) (ringChar.eq F 2)
    have hp := Fintype.card_pos (α := F)
    have hm : (Fintype.card F - 1) % 2 = 1 := by omega
    rw [hm, Nat.cast_one]
  let v : Mat F := ∑ b : Fˣ, f.val (torus b)
  refine ⟨v, fun a => ?_⟩
  have hs : ∑ b : Fˣ, f.val (torus (a * b)) = v := by
    exact Equiv.sum_comp (Equiv.mulLeft a) (fun b => f.val (torus b))
  simp only [torus_mul, cocycle_mul, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, ← map_sum, ← Nat.cast_smul_eq_nsmul F, hcard, one_smul] at hs
  change f.val (torus a) - (tensorAction σ (torus a) v - v) = 0
  apply sub_eq_zero.mpr
  rw [eq_sub_iff_add_eq]
  calc
    f.val (torus a) + v = f.val (torus a) + (tensorAction σ (torus a) v + f.val (torus a)) := by rw [hs]
    _ = tensorAction σ (torus a) v := by
      ext i j
      change f.val (torus a) i j + (tensorAction σ (torus a) v i j + f.val (torus a) i j) = _
      rw [add_comm (tensorAction σ (torus a) v i j), CharTwo.add_cancel_left]

private lemma upper_d (σ : F ≃+* F) (f : cocycles (tensorAction σ)) (t : F) :
    f.val (upper t) 1 1 = 0 := by
  by_cases ht : t = 0
  · subst t
    simp [upper, transvection_coeff_zero, cocycle_one]
  · have h := congrArg (fun X : Mat F => X 0 1) (f.property (upper t) (upper t))
    rw [upper_square, cocycle_one, upper_apply] at h
    have he : t * f.val (upper t) 1 1 = 0 := by
      simpa [add_comm, add_left_comm, CharTwo.add_self_eq_zero, CharTwo.add_cancel_left] using h.symm
    exact (mul_eq_zero.mp he).resolve_left ht

private lemma upper_bc (σ : F ≃+* F) (f : cocycles (tensorAction σ)) (t : F) :
    t * f.val (upper t) 1 0 = σ t * f.val (upper t) 0 1 := by
  have h := congrArg (fun X : Mat F => X 0 0) (f.property (upper t) (upper t))
  rw [upper_square, cocycle_one, upper_apply] at h
  apply CharTwo.add_eq_zero.mp
  simpa [upper_d, add_assoc, add_comm, add_left_comm, CharTwo.add_self_eq_zero, CharTwo.add_cancel_left] using h.symm

private lemma upper_b_add (σ : F ≃+* F) (f : cocycles (tensorAction σ)) (s t : F) :
    f.val (upper (s + t)) 0 1 = f.val (upper s) 0 1 + f.val (upper t) 0 1 := by
  have h := congrArg (fun X : Mat F => X 0 1) (f.property (upper s) (upper t))
  rw [← transvection_add, upper_apply] at h
  simpa [upper_d, add_comm] using h

private lemma upper_sum_bc (σ : F ≃+* F) (f : cocycles (tensorAction σ)) (t : F) :
    f.val (upper t) 1 0 + f.val (upper t) 0 1 =
      f.val (upper 1) 0 1 * (t + σ t) := by
  have hcomm : upper t * upper (1 : F) = upper 1 * upper t := by
    rw [← transvection_add, ← transvection_add, add_comm t]
  have h := congrArg (fun g => f.val g 0 0) hcomm
  simp only [cocycle_mul, upper_apply, Matrix.add_apply, upper_d, mul_zero, add_zero,
    map_one, one_mul] at h
  have h1 : f.val (upper 1) 1 0 = f.val (upper 1) 0 1 := by
    simpa using upper_bc σ f 1
  simp only [h1, Matrix.of_apply, Matrix.cons_val_zero] at h
  linear_combination -h

private lemma upper_b (σ : F ≃+* F) (hσ : ∃ s : F, σ s ≠ s)
    (f : cocycles (tensorAction σ)) (t : F) :
    f.val (upper t) 0 1 = f.val (upper 1) 0 1 * t := by
  have hgood (x : F) (hx : σ x ≠ x) :
      f.val (upper x) 0 1 = f.val (upper 1) 0 1 * x := by
    have he : (x + σ x) * (f.val (upper x) 0 1 - f.val (upper 1) 0 1 * x) = 0 := by
      linear_combination x * upper_sum_bc σ f x - upper_bc σ f x
    have hx' : x + σ x ≠ 0 := by
      intro h
      exact hx (CharTwo.add_eq_zero.mp h).symm
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hx')
  by_cases ht : σ t = t
  · obtain ⟨s, hs⟩ := hσ
    have hst : σ (s + t) ≠ s+t := by
      simpa only [map_add, ht, ne_eq, add_left_inj] using hs
    linear_combination hgood (s + t) hst - hgood s hs - upper_b_add σ f s t
  · exact hgood t ht

private lemma upper_c (σ : F ≃+* F) (hσ : ∃ s : F, σ s ≠ s)
    (f : cocycles (tensorAction σ)) (t : F) :
    f.val (upper t) 1 0 = f.val (upper 1) 0 1 * σ t := by
  have h := upper_sum_bc σ f t
  rw [upper_b σ hσ] at h
  linear_combination h

omit [CharP F 2] in
private lemma upper_covariance (σ : F ≃+* F) (f : cocycles (tensorAction σ))
    (hf : ∀ a : Fˣ, f.val (torus a) = 0) (a : Fˣ) (t : F) :
    f.val (upper ((a : F)^2 * t)) = tensorAction σ (torus a) (f.val (upper t)) := by
  have h := congrArg f.val (torus_upper a t)
  simpa only [cocycle_mul, hf, map_zero, zero_add, add_zero] using h.symm

private lemma upper_beta_weight (σ : F ≃+* F) (hσ : ∃ s : F, σ s ≠ s)
    (f : cocycles (tensorAction σ)) (hf : ∀ a : Fˣ, f.val (torus a) = 0) (a : Fˣ) :
    (a : F) * σ a * f.val (upper 1) 0 1 = f.val (upper 1) 0 1 := by
  have h := congrArg (fun X : Mat F => X 0 1) (upper_covariance σ f hf a 1)
  rw [torus_apply] at h
  rw [upper_b σ hσ f ((a : F)^2 * 1)] at h
  simp only [mul_one, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h
  have ha : σ (a : F) ≠ 0 := (map_ne_zero σ).mpr a.ne_zero
  have he := congrArg (fun x : F => (a : F)⁻¹ * σ a * x) h
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm, a.ne_zero, ha] using he

private lemma upper_lambda_add (σ : F ≃+* F) (hσ : ∃ s : F, σ s ≠ s)
    (f : cocycles (tensorAction σ)) (s t : F) :
    f.val (upper (s + t)) 0 0 + f.val (upper 1) 0 1 * (s + t) * σ (s + t) =
      (f.val (upper s) 0 0 + f.val (upper 1) 0 1 * s * σ s) +
      (f.val (upper t) 0 0 + f.val (upper 1) 0 1 * t * σ t) := by
  have h := congrArg (fun X : Mat F => X 0 0) (f.property (upper s) (upper t))
  rw [← transvection_add, upper_apply] at h
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.cons_val_zero,
    upper_d, mul_zero, add_zero] at h
  rw [upper_b σ hσ f t, upper_c σ hσ f t] at h
  rw [map_add]
  generalize hb : f.val (upper 1) 0 1 = b at h ⊢
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [htwo])) h

private lemma upper_lambda_square (σ : F ≃+* F) (hσ : ∃ s : F, σ s ≠ s)
    (f : cocycles (tensorAction σ)) (hf : ∀ a : Fˣ, f.val (torus a) = 0) (a : F) :
    f.val (upper (a ^ 2)) 0 0 + f.val (upper 1) 0 1 * a ^ 2 * σ (a ^ 2) =
      a * σ a * (f.val (upper 1) 0 0 + f.val (upper 1) 0 1) := by
  by_cases ha : a = 0
  · subst a
    simp [upper, transvection_coeff_zero, cocycle_one]
  · let u : Fˣ := Units.mk0 a ha
    have h := congrArg (fun X : Mat F => X 0 0) (upper_covariance σ f hf u 1)
    rw [torus_apply] at h
    simp only [mul_one, Matrix.of_apply, Matrix.cons_val_zero] at h
    change f.val (upper (a ^ 2)) 0 0 = a * σ a * f.val (upper 1) 0 0 at h
    have hb := upper_beta_weight σ hσ f hf u
    change a * σ a * f.val (upper 1) 0 1 = f.val (upper 1) 0 1 at hb
    rw [map_pow]
    linear_combination h + a * σ a * hb

private lemma upper_a [Finite F] (σ : F ≃+* F) (hσ : ∃ s : F, σ s ≠ s)
    (f : cocycles (tensorAction σ)) (hf : ∀ a : Fˣ, f.val (torus a) = 0) (t : F) :
    f.val (upper t) 0 0 = f.val (upper 1) 0 1 * t * σ t := by
  let lam (x : F) := f.val (upper x) 0 0 + f.val (upper 1) 0 1 * x * σ x
  have hadd (s t : F) : lam (s + t) = lam s + lam t := upper_lambda_add σ hσ f s t
  have hsquare (a : F) : lam (a ^ 2) = a * σ a * lam 1 := by
    simpa only [lam, map_one, mul_one] using upper_lambda_square σ hσ f hf a
  have h1 : lam 1 = 0 := by
    obtain ⟨a, ha⟩ := hσ
    have he := hadd (a ^ 2) 1
    rw [← one_pow 2, ← CharTwo.add_sq, hsquare, hsquare, hsquare] at he
    simp only [map_add, map_one, one_mul] at he
    have hz : (a + σ a) * lam 1 = 0 := by linear_combination he
    exact (mul_eq_zero.mp hz).resolve_left (by
      intro h
      exact ha (CharTwo.add_eq_zero.mp h).symm)
  have ht := hsquare ((frobeniusEquiv F 2).symm t)
  rw [frobeniusEquiv_symm_pow_p, h1, mul_zero] at ht
  exact CharTwo.add_eq_zero.mp ht

private lemma exists_borel_normalized [Finite F] (σ : F ≃+* F)
    (hσ : ∃ s : F, σ s ≠ s) (f : cocycles (tensorAction σ))
    (hf : ∀ a : Fˣ, f.val (torus a) = 0) :
    ∃ v : Mat F, (∀ a : Fˣ, (f - principal (tensorAction σ) v).val (torus a) = 0) ∧
      ∀ t : F, (f - principal (tensorAction σ) v).val (upper t) = 0 := by
  let b := f.val (upper 1) 0 1
  let v : Mat F := !![0,0;0,b]
  refine ⟨v, ?_, ?_⟩
  · intro a
    have hb := upper_beta_weight σ hσ f hf a⁻¹
    simp only [Units.val_inv_eq_inv_val, map_inv₀] at hb
    change f.val (torus a) - (tensorAction σ (torus a) v - v) = 0
    rw [hf, torus_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [v, b, hb]
  · intro t
    change f.val (upper t) - (tensorAction σ (upper t) v - v) = 0
    rw [upper_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [v, b, upper_a σ hσ f hf t, upper_b σ hσ f t, upper_c σ hσ f t,
        upper_d, mul_comm, mul_left_comm, mul_assoc]

private lemma normalized_swap_shape (σ : F ≃+* F) (hσ : ∃ s : F, σ s ≠ s)
    (f : cocycles (tensorAction σ)) (hf : ∀ a : Fˣ, f.val (torus a) = 0) :
    f.val swap = !![f.val swap 0 0, 0; 0, f.val swap 0 0] ∧
      ∀ a : Fˣ, (a : F) * σ a * f.val swap 0 0 = f.val swap 0 0 := by
  have hfix (a : Fˣ) : tensorAction σ (torus a) (f.val swap) = f.val swap := by
    have h := congrArg f.val (torus_swap a)
    simpa only [cocycle_mul, hf, map_zero, add_zero, zero_add] using h
  have hs := f.property swap swap
  rw [swap_square, cocycle_one, swap_apply] at hs
  have hdiag : f.val swap 1 1 = f.val swap 0 0 := by
    apply CharTwo.add_eq_zero.mp
    simpa using (congrArg (fun X : Mat F => X 0 0) hs).symm
  have hoff : f.val swap 1 0 = f.val swap 0 1 := by
    apply CharTwo.add_eq_zero.mp
    simpa using (congrArg (fun X : Mat F => X 0 1) hs).symm
  have hb : f.val swap 0 1 = 0 := by
    obtain ⟨t, ht⟩ := hσ
    have ht0 : t ≠ 0 := by rintro rfl; exact ht (map_zero σ)
    have hσt0 := (map_ne_zero σ).mpr ht0
    have he := congrArg (fun X : Mat F => X 0 1) (hfix (Units.mk0 t ht0))
    rw [torus_apply] at he
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Units.val_mk0] at he
    have he' : t * f.val swap 0 1 = σ t * f.val swap 0 1 := by
      have h := congrArg (fun x : F => σ t * x) he
      simpa [mul_assoc, mul_comm, mul_left_comm, hσt0] using h
    exact (mul_eq_zero.mp (by linear_combination he' :
      (t - σ t) * f.val swap 0 1 = 0)).resolve_left (sub_ne_zero.mpr ht.symm)
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hdiag, hoff, hb]
  · intro a
    have h := congrArg (fun X : Mat F => X 0 0) (hfix a)
    rw [torus_apply] at h
    exact h

private lemma borel_normalized_principal (σ : F ≃+* F) (hσ : ∃ s : F, σ s ≠ s)
    (f : cocycles (tensorAction σ)) (hf : ∀ a : Fˣ, f.val (torus a) = 0)
    (hu : ∀ t : F, f.val (upper t) = 0) :
    ∃ v : Mat F, principal (tensorAction σ) v = f := by
  obtain ⟨hs, hw⟩ := normalized_swap_shape σ hσ f hf
  let v : Mat F := !![f.val swap 0 0,0;0,0]
  let d := f - principal (tensorAction σ) v
  have hdU (t : F) : d.val (upper t) = 0 := by
    change f.val (upper t) - (tensorAction σ (upper t) v - v) = 0
    rw [hu, upper_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [v]
  have hdW : d.val swap = 0 := by
    change f.val swap - (tensorAction σ swap v - v) = 0
    rw [swap_apply, hs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [v, CharTwo.sub_eq_add]
  have hdL (t : F) : d.val (lower t) = 0 := by
    have h := congrArg d.val (swap_upper t)
    simpa only [cocycle_mul, hdU, hdW, map_zero, add_zero, zero_add] using h.symm
  have hd : d = 0 := by
    apply Subtype.ext
    funext g
    apply Matrix.SL2.transvection_induction (fun g => d.val g = 0) ?_ ?_ g
    · intro i j hij t
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hdU t
      · exact hdL t
      · exact (hij rfl).elim
    · intro g h hg hh
      rw [d.property, hg, hh, map_zero, add_zero]
  exact ⟨v, (sub_eq_zero.mp hd).symm⟩

/-- Every cocycle of the twisted tensor action is principal over a finite
characteristic-two field with a nonidentity coefficient automorphism. -/
public theorem tensorAction_principal_surjective [Finite F] (σ : F ≃+* F)
    (hσ : ∃ t : F, σ t ≠ t) :
    Function.Surjective (principal (tensorAction σ)) := by
  intro f
  obtain ⟨vT, hT⟩ := exists_torus_normalized σ f
  obtain ⟨vU, hTU, hU⟩ := exists_borel_normalized σ hσ (f - principal _ vT) hT
  obtain ⟨vW, hW⟩ := borel_normalized_principal σ hσ _ hTU hU
  refine ⟨vW + vU + vT, ?_⟩
  rw [map_add, map_add, hW]
  abel

/-- Ambient first-cohomology vanishing for the quadratic Frobenius tensor,
including the extension of degree two (the field with four elements). -/
public theorem tensorAction_frobenius_principal_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (principal (tensorAction
      (iterateFrobeniusEquiv (GaloisField 2 (2 * n)) 2 n))) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact tensorAction_principal_surjective _ (FiniteModel.exists_conjugation_ne n)

/-- The quadratic Frobenius tensor has no ambient fixed vectors. -/
public theorem tensorAction_frobenius_fixed_eq_bot (n : ℕ) (hn : 0 < n) :
    OneCohomology.fixed (tensorAction
      (iterateFrobeniusEquiv (GaloisField 2 (2 * n)) 2 n)) = ⊥ := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact tensorAction_fixed_eq_bot _ (FiniteModel.exists_conjugation_ne n)

end Representation.OrthogonalFourMinus

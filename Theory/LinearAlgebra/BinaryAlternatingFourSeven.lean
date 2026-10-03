module

public import Theory.LinearAlgebra.BinarySymplecticSevenNondegenerate

/-!
A finite certificate for degenerate alternating binary forms in dimension four.
The singular nonzero forms have rank two. Explicit changes of basis reduce them
to `J2`; a compact row certificate excludes seventh-order actors for this form.
Combining the result with the existing symplectic certificate handles every
nonzero alternating form, as needed for the small 2-group commutator argument.
-/

open Matrix

namespace BinaryAlternatingFour

private def J2 : Mat := !![0,1,0,0; 1,0,0,0; 0,0,0,0; 0,0,0,0]

private def singularNormalizer (aa bb cc dd ee ff : ZMod 2) : Mat :=
  match aa.val, bb.val, cc.val, dd.val, ee.val, ff.val with
  | 0, 0, 0, 0, 0, 1 => !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]
  | 0, 0, 0, 0, 1, 0 => !![0,0,1,0; 1,0,0,0; 0,0,0,1; 0,1,0,0]
  | 0, 0, 0, 0, 1, 1 => !![0,0,1,0; 1,0,0,1; 0,0,0,1; 0,1,0,0]
  | 0, 0, 0, 1, 0, 0 => !![0,0,1,0; 1,0,0,0; 0,1,0,0; 0,0,0,1]
  | 0, 0, 0, 1, 0, 1 => !![0,0,1,0; 1,0,0,1; 0,1,0,0; 0,0,0,1]
  | 0, 0, 0, 1, 1, 0 => !![0,0,1,0; 1,0,0,0; 0,1,0,1; 0,0,0,1]
  | 0, 0, 0, 1, 1, 1 => !![0,0,1,0; 1,0,0,1; 0,1,0,1; 0,0,0,1]
  | 0, 0, 1, 0, 0, 0 => !![1,0,0,0; 0,0,1,0; 0,0,0,1; 0,1,0,0]
  | 0, 0, 1, 0, 0, 1 => !![1,0,0,1; 0,0,1,0; 0,0,0,1; 0,1,0,0]
  | 0, 0, 1, 0, 1, 0 => !![1,0,1,0; 0,0,1,0; 0,0,0,1; 0,1,0,0]
  | 0, 0, 1, 0, 1, 1 => !![1,0,1,1; 0,0,1,0; 0,0,0,1; 0,1,0,0]
  | 0, 1, 0, 0, 0, 0 => !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]
  | 0, 1, 0, 0, 0, 1 => !![1,0,0,1; 0,0,1,0; 0,1,0,0; 0,0,0,1]
  | 0, 1, 0, 1, 0, 0 => !![1,0,1,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]
  | 0, 1, 0, 1, 0, 1 => !![1,0,1,1; 0,0,1,0; 0,1,0,0; 0,0,0,1]
  | 0, 1, 1, 0, 0, 0 => !![1,0,0,0; 0,0,1,0; 0,1,0,1; 0,0,0,1]
  | 0, 1, 1, 0, 0, 1 => !![1,0,0,1; 0,0,1,0; 0,1,0,1; 0,0,0,1]
  | 0, 1, 1, 1, 1, 0 => !![1,0,1,0; 0,0,1,0; 0,1,0,1; 0,0,0,1]
  | 0, 1, 1, 1, 1, 1 => !![1,0,1,1; 0,0,1,0; 0,1,0,1; 0,0,0,1]
  | 1, 0, 0, 0, 0, 0 => !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]
  | 1, 0, 0, 0, 1, 0 => !![1,0,0,1; 0,1,0,0; 0,0,1,0; 0,0,0,1]
  | 1, 0, 0, 1, 0, 0 => !![1,0,1,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]
  | 1, 0, 0, 1, 1, 0 => !![1,0,1,1; 0,1,0,0; 0,0,1,0; 0,0,0,1]
  | 1, 0, 1, 0, 0, 0 => !![1,0,0,0; 0,1,0,1; 0,0,1,0; 0,0,0,1]
  | 1, 0, 1, 0, 1, 0 => !![1,0,0,1; 0,1,0,1; 0,0,1,0; 0,0,0,1]
  | 1, 0, 1, 1, 0, 1 => !![1,0,1,0; 0,1,0,1; 0,0,1,0; 0,0,0,1]
  | 1, 0, 1, 1, 1, 1 => !![1,0,1,1; 0,1,0,1; 0,0,1,0; 0,0,0,1]
  | 1, 1, 0, 0, 0, 0 => !![1,0,0,0; 0,1,1,0; 0,0,1,0; 0,0,0,1]
  | 1, 1, 0, 0, 1, 1 => !![1,0,0,1; 0,1,1,0; 0,0,1,0; 0,0,0,1]
  | 1, 1, 0, 1, 0, 0 => !![1,0,1,0; 0,1,1,0; 0,0,1,0; 0,0,0,1]
  | 1, 1, 0, 1, 1, 1 => !![1,0,1,1; 0,1,1,0; 0,0,1,0; 0,0,0,1]
  | 1, 1, 1, 0, 0, 0 => !![1,0,0,0; 0,1,1,1; 0,0,1,0; 0,0,0,1]
  | 1, 1, 1, 0, 1, 1 => !![1,0,0,1; 0,1,1,1; 0,0,1,0; 0,0,0,1]
  | 1, 1, 1, 1, 0, 1 => !![1,0,1,0; 0,1,1,1; 0,0,1,0; 0,0,0,1]
  | 1, 1, 1, 1, 1, 0 => !![1,0,1,1; 0,1,1,1; 0,0,1,0; 0,0,0,1]
  | _, _, _, _, _, _ => 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem singularNormalizer_certificate : ∀ aa bb cc dd ee ff : ZMod 2,
    alternating aa bb cc dd ee ff = 0 ∨
      (alternating aa bb cc dd ee ff).det ≠ 0 ∨
      ((singularNormalizer aa bb cc dd ee ff).det ≠ 0 ∧
        (singularNormalizer aa bb cc dd ee ff).transpose * alternating aa bb cc dd ee ff *
          singularNormalizer aa bb cc dd ee ff = J2) := by
  decide

private theorem exists_singular_congruence (form : Mat)
    (hdiag : ∀ index, form index index = 0) (hsymm : form = form.transpose)
    (hne : form ≠ 0) (hdet : form.det = 0) :
    ∃ basis : Mat, basis.det ≠ 0 ∧ basis.transpose * form * basis = J2 := by
  rw [matrix_eq_alternating form hdiag hsymm] at hne hdet ⊢
  exact ⟨_, ((singularNormalizer_certificate _ _ _ _ _ _).resolve_left hne).resolve_left
    (not_not.mpr hdet)⟩

private def pairing2 (left right : Fin 4 → ZMod 2) : ZMod 2 :=
  left 0 * right 1 + left 1 * right 0

private def seventh (actor : Mat) : Mat :=
  BinarySymplecticSeven.fastMul (BinarySymplecticSeven.fourth actor)
    (BinarySymplecticSeven.fastMul (BinarySymplecticSeven.fastMul actor actor) actor)

private def finalCheck (aa bb cc dd : Fin 16) : Prop :=
  BinarySymplecticSeven.entriesEqual
    (seventh (BinarySymplecticSeven.decode aa bb cc dd).transpose) 1 →
  BinarySymplecticSeven.entriesEqual (BinarySymplecticSeven.decode aa bb cc dd).transpose 1

private instance (aa bb cc dd : Fin 16) : Decidable (finalCheck aa bb cc dd) := by
  unfold finalCheck
  infer_instance

private def fourthRow (aa bb cc : Fin 16) : Prop :=
  ∀ dd : Fin 16, pairing2 (BinarySymplecticSeven.row aa) (BinarySymplecticSeven.row dd) = 0 →
    pairing2 (BinarySymplecticSeven.row bb) (BinarySymplecticSeven.row dd) = 0 →
    finalCheck aa bb cc dd

private instance (aa bb cc : Fin 16) : Decidable (fourthRow aa bb cc) := by
  unfold fourthRow
  infer_instance

private def thirdRow (aa bb : Fin 16) : Prop :=
  ∀ cc : Fin 16, pairing2 (BinarySymplecticSeven.row aa) (BinarySymplecticSeven.row cc) = 0 →
    pairing2 (BinarySymplecticSeven.row bb) (BinarySymplecticSeven.row cc) = 0 → fourthRow aa bb cc

private instance (aa bb : Fin 16) : Decidable (thirdRow aa bb) := by
  unfold thirdRow
  infer_instance

private def secondRow (aa : Fin 16) : Prop :=
  ∀ bb : Fin 16, pairing2 (BinarySymplecticSeven.row aa) (BinarySymplecticSeven.row bb) = 1 →
    thirdRow aa bb

private instance (aa : Fin 16) : Decidable (secondRow aa) := by
  unfold secondRow
  infer_instance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem rank_two_certificate : ∀ aa bb : Fin 16,
    pairing2 (BinarySymplecticSeven.row aa) (BinarySymplecticSeven.row bb) = 1 →
    ∀ cc : Fin 16,
    pairing2 (BinarySymplecticSeven.row aa) (BinarySymplecticSeven.row cc) = 0 →
    pairing2 (BinarySymplecticSeven.row bb) (BinarySymplecticSeven.row cc) = 0 →
    ∀ dd : Fin 16,
    pairing2 (BinarySymplecticSeven.row aa) (BinarySymplecticSeven.row dd) = 0 →
    pairing2 (BinarySymplecticSeven.row bb) (BinarySymplecticSeven.row dd) = 0 →
    (∀ ii jj, seventh (BinarySymplecticSeven.decode aa bb cc dd).transpose ii jj =
      (1 : Mat) ii jj) →
    ∀ ii jj, (BinarySymplecticSeven.decode aa bb cc dd).transpose ii jj = (1 : Mat) ii jj := by
  change ∀ aa, secondRow aa
  decide

private theorem pairing2_eq_mul (actor : Mat) (ii jj : Fin 4) :
    pairing2 (actor ii) (actor jj) = (actor * J2 * actor.transpose) ii jj := by
  simp [pairing2, Matrix.mul_apply, Fin.sum_univ_succ, J2]
  ring

private theorem seventh_eq_pow (actor : Mat) : seventh actor = actor ^ 7 := by
  simp [seventh, BinarySymplecticSeven.fourth, BinarySymplecticSeven.fastMul_eq,
    pow_succ, mul_assoc]

private theorem rank_two_order_seven_eq_one (actor : Mat)
    (hpower : actor ^ 7 = 1) (hpres : actor.transpose * J2 * actor = J2) :
    actor = 1 := by
  obtain ⟨aa, bb, cc, dd, hdecode⟩ := BinarySymplecticSeven.decode_surjective actor.transpose
  have hactor : actor = (BinarySymplecticSeven.decode aa bb cc dd).transpose := by
    rw [hdecode, Matrix.transpose_transpose]
  rw [hactor] at hpower hpres ⊢
  simp only [Matrix.transpose_transpose] at hpres
  have hp (ii jj : Fin 4) :
      pairing2 (BinarySymplecticSeven.decode aa bb cc dd ii)
        (BinarySymplecticSeven.decode aa bb cc dd jj) = J2 ii jj := by
    rw [pairing2_eq_mul, hpres]
  apply Matrix.ext
  apply rank_two_certificate aa bb (by simpa [BinarySymplecticSeven.decode, J2] using hp 0 1)
    cc (by simpa [BinarySymplecticSeven.decode, J2] using hp 0 2)
    (by simpa [BinarySymplecticSeven.decode, J2] using hp 1 2)
    dd (by simpa [BinarySymplecticSeven.decode, J2] using hp 0 3)
    (by simpa [BinarySymplecticSeven.decode, J2] using hp 1 3)
  intro ii jj
  rw [seventh_eq_pow, hpower]

private theorem rank_two_conjugate_preserves (form basis inverse actor : Mat)
    (hinverse : basis * inverse = 1)
    (hcongr : basis.transpose * form * basis = J2)
    (hpres : actor.transpose * form * actor = form) :
    (inverse * actor * basis).transpose * J2 * (inverse * actor * basis) = J2 := by
  calc
    _ = basis.transpose * actor.transpose * (basis * inverse).transpose * form *
        (basis * inverse) * actor * basis := by
      rw [← hcongr]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = basis.transpose * (actor.transpose * form * actor) * basis := by
      simp only [hinverse, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc]
    _ = J2 := by rw [hpres, hcongr]

/-- A nonzero alternating binary form in dimension four admits no nontrivial
isometry whose seventh power is the identity, including when the form is singular. -/
public theorem nonzero_form_order_seven_eq_one (form actor : Mat)
    (hne : form ≠ 0) (halt : form.toBilin'.IsAlt)
    (hpower : actor ^ 7 = 1) (hpres : actor.transpose * form * actor = form) :
    actor = 1 := by
  by_cases hdet : form.det = 0
  · obtain ⟨basis, hdetBasis, hcongr⟩ := exists_singular_congruence form
      (fun index => by
        simpa only [Matrix.toBilin'_single] using halt.self_eq_zero (Pi.single index 1))
      (by
        ext row col
        simpa only [Matrix.toBilin'_single, ZMod.neg_eq_self_mod_two,
          Matrix.transpose_apply] using halt.neg_eq (Pi.single row 1) (Pi.single col 1))
      hne hdet
    have hunit : IsUnit basis.det := isUnit_iff_ne_zero.mpr hdetBasis
    have hright := Matrix.mul_nonsing_inv basis hunit
    have hleft := Matrix.nonsing_inv_mul basis hunit
    apply (conjugate_eq_one_iff basis basis⁻¹ actor hright hleft).mp
    apply rank_two_order_seven_eq_one
    · rw [conjugate_pow _ _ _ hleft hright, hpower, Matrix.mul_one, hleft]
    · exact rank_two_conjugate_preserves _ _ _ _ hright hcongr hpres
  · exact BinarySymplecticSeven.arbitrary_form_order_seven_eq_one form actor halt
      (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet) hpower hpres

end BinaryAlternatingFour

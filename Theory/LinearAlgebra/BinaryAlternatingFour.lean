module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
Explicit changes of basis carry every nonsingular alternating binary four-
dimensional form to the standard symplectic form. The finite table is kernel-
checked, and conjugation transports both the preservation equation and finite-
order equations. This is the nondegenerate branch of the small 2-group
commutator-form obstruction.
-/

public section

open Matrix

namespace BinaryAlternatingFour

abbrev Mat := Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def J4 : Mat := !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]

@[expose] def alternating (aa bb cc dd ee ff : ZMod 2) : Mat :=
  !![0,aa,bb,cc; aa,0,dd,ee; bb,dd,0,ff; cc,ee,ff,0]

def normalizer (aa bb cc dd ee ff : ZMod 2) : Mat :=
  match aa.val, bb.val, cc.val, dd.val, ee.val, ff.val with
  | 0, 0, 1, 1, 0, 0 => !![0,1,0,0; 0,0,0,1; 0,0,1,0; 1,0,0,0]
  | 0, 0, 1, 1, 0, 1 => !![0,0,0,1; 0,0,1,0; 0,1,0,1; 1,0,1,0]
  | 0, 0, 1, 1, 1, 0 => !![0,0,0,1; 0,1,0,1; 0,0,1,0; 1,0,1,0]
  | 0, 0, 1, 1, 1, 1 => !![0,0,0,1; 0,0,1,0; 0,1,1,1; 1,0,1,0]
  | 0, 1, 0, 0, 1, 0 => !![0,0,0,1; 0,1,0,0; 0,0,1,0; 1,0,0,0]
  | 0, 1, 0, 0, 1, 1 => !![0,0,0,1; 0,0,1,0; 0,1,1,0; 1,0,0,1]
  | 0, 1, 0, 1, 1, 0 => !![0,0,0,1; 0,1,0,0; 0,0,1,0; 1,0,1,0]
  | 0, 1, 0, 1, 1, 1 => !![0,0,0,1; 0,0,1,0; 0,1,1,0; 1,0,1,1]
  | 0, 1, 1, 0, 1, 0 => !![0,0,0,1; 0,1,0,1; 0,0,1,0; 1,0,0,0]
  | 0, 1, 1, 0, 1, 1 => !![0,0,0,1; 0,0,1,0; 0,1,1,1; 1,0,0,1]
  | 0, 1, 1, 1, 0, 0 => !![0,1,0,0; 0,0,0,1; 0,0,1,0; 1,0,1,0]
  | 0, 1, 1, 1, 0, 1 => !![0,0,0,1; 0,0,1,0; 0,1,0,1; 1,0,1,1]
  | 1, 0, 0, 0, 0, 1 => !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,0]
  | 1, 0, 0, 0, 1, 1 => !![0,0,0,1; 0,0,1,0; 0,1,1,0; 1,0,0,0]
  | 1, 0, 0, 1, 0, 1 => !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,1,0]
  | 1, 0, 0, 1, 1, 1 => !![0,0,0,1; 0,0,1,0; 0,1,1,0; 1,0,1,0]
  | 1, 0, 1, 0, 0, 1 => !![0,0,0,1; 0,0,1,0; 0,1,0,1; 1,0,0,0]
  | 1, 0, 1, 0, 1, 1 => !![0,0,0,1; 0,0,1,0; 0,1,1,1; 1,0,0,0]
  | 1, 0, 1, 1, 0, 0 => !![0,1,0,0; 0,0,0,1; 0,0,1,0; 1,0,0,1]
  | 1, 0, 1, 1, 1, 0 => !![0,0,0,1; 0,1,0,1; 0,0,1,0; 1,0,1,1]
  | 1, 1, 0, 0, 0, 1 => !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,1]
  | 1, 1, 0, 0, 1, 0 => !![0,0,0,1; 0,1,0,0; 0,0,1,0; 1,0,0,1]
  | 1, 1, 0, 1, 0, 1 => !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,1,1]
  | 1, 1, 0, 1, 1, 0 => !![0,0,0,1; 0,1,0,0; 0,0,1,0; 1,0,1,1]
  | 1, 1, 1, 0, 0, 1 => !![0,0,0,1; 0,0,1,0; 0,1,0,1; 1,0,0,1]
  | 1, 1, 1, 0, 1, 0 => !![0,0,0,1; 0,1,0,1; 0,0,1,0; 1,0,0,1]
  | 1, 1, 1, 1, 0, 0 => !![0,1,0,0; 0,0,0,1; 0,0,1,0; 1,0,1,1]
  | 1, 1, 1, 1, 1, 1 => !![0,0,0,1; 0,0,1,0; 0,1,1,1; 1,0,1,1]
  | _, _, _, _, _, _ => 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem normalizer_certificate : ∀ aa bb cc dd ee ff : ZMod 2,
    (alternating aa bb cc dd ee ff).det = 0 ∨
      ((normalizer aa bb cc dd ee ff).det ≠ 0 ∧
        (normalizer aa bb cc dd ee ff).transpose * alternating aa bb cc dd ee ff *
          normalizer aa bb cc dd ee ff = J4) := by
  decide

theorem matrix_eq_alternating (form : Mat) (hdiag : ∀ index, form index index = 0)
    (hsymm : form = form.transpose) :
    form = alternating (form 0 1) (form 0 2) (form 0 3)
      (form 1 2) (form 1 3) (form 2 3) := by
  have hswap (row col : Fin 4) : form row col = form col row :=
    congr_fun (congr_fun hsymm row) col
  ext row col
  fin_cases row <;> fin_cases col <;> simp [alternating, hdiag, hswap] <;> exact hswap _ _

theorem exists_congruence_of_det_ne_zero (form : Mat)
    (hdiag : ∀ index, form index index = 0) (hsymm : form = form.transpose)
    (hdet : form.det ≠ 0) :
    ∃ basis : Mat, basis.det ≠ 0 ∧ basis.transpose * form * basis = J4 := by
  rw [matrix_eq_alternating form hdiag hsymm] at hdet ⊢
  exact ⟨_, (normalizer_certificate _ _ _ _ _ _).resolve_left hdet⟩

theorem exists_congruence (form : Mat) (halt : form.toBilin'.IsAlt)
    (hnondegenerate : form.toBilin'.Nondegenerate) :
    ∃ basis : Mat, basis.det ≠ 0 ∧ basis.transpose * form * basis = J4 := by
  apply exists_congruence_of_det_ne_zero form
  · intro index
    simpa only [Matrix.toBilin'_single] using halt.self_eq_zero (Pi.single index 1)
  · ext row col
    simpa only [Matrix.toBilin'_single, ZMod.neg_eq_self_mod_two,
      Matrix.transpose_apply] using
      halt.neg_eq (Pi.single row 1) (Pi.single col 1)
  · exact LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mp hnondegenerate

theorem conjugate_preserves (form basis inverse actor : Mat)
    (hinverse : basis * inverse = 1)
    (hcongr : basis.transpose * form * basis = J4)
    (hpres : actor.transpose * form * actor = form) :
    (inverse * actor * basis).transpose * J4 * (inverse * actor * basis) = J4 := by
  calc
    _ = basis.transpose * actor.transpose * (basis * inverse).transpose * form *
        (basis * inverse) * actor * basis := by
      rw [← hcongr]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = basis.transpose * (actor.transpose * form * actor) * basis := by
      simp only [hinverse, Matrix.transpose_one, Matrix.mul_one,
        Matrix.mul_assoc]
    _ = J4 := by rw [hpres, hcongr]

theorem conjugate_pow (basis inverse actor : Mat)
    (hleft : inverse * basis = 1) (hright : basis * inverse = 1) (power : ℕ) :
    (inverse * actor * basis) ^ power = inverse * actor ^ power * basis := by
  induction power with
  | zero => simp [hleft]
  | succ power ih =>
    rw [pow_succ, pow_succ, ih]
    calc
      _ = inverse * actor ^ power * (basis * inverse) * actor * basis := by
        simp only [Matrix.mul_assoc]
      _ = _ := by simp only [hright, Matrix.mul_one, Matrix.mul_assoc]

theorem conjugate_eq_one_iff (basis inverse actor : Mat)
    (hright : basis * inverse = 1) (hleft : inverse * basis = 1) :
    inverse * actor * basis = 1 ↔ actor = 1 := by
  constructor
  · intro heq
    have hcancel := congrArg (fun matrix : Mat => basis * matrix * inverse) heq
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc basis inverse, hright,
      Matrix.one_mul, Matrix.mul_one] using hcancel
  · rintro rfl
    simpa only [Matrix.mul_one] using hleft

theorem transport_preserving_actor (form actor : Mat)
    (halt : form.toBilin'.IsAlt) (hnondegenerate : form.toBilin'.Nondegenerate)
    (hpres : actor.transpose * form * actor = form) :
    ∃ standardActor : Mat,
      standardActor.transpose * J4 * standardActor = J4 ∧
      (∀ power : ℕ, actor ^ power = 1 → standardActor ^ power = 1) ∧
      (standardActor = 1 ↔ actor = 1) := by
  obtain ⟨basis, hdet, hcongr⟩ := exists_congruence form halt hnondegenerate
  have hunit : IsUnit basis.det := isUnit_iff_ne_zero.mpr hdet
  have hright := Matrix.mul_nonsing_inv basis hunit
  have hleft := Matrix.nonsing_inv_mul basis hunit
  refine ⟨basis⁻¹ * actor * basis, conjugate_preserves _ _ _ _ hright hcongr hpres, ?_,
    conjugate_eq_one_iff _ _ _ hright hleft⟩
  intro power hpower
  rw [conjugate_pow _ _ _ hleft hright, hpower, Matrix.mul_one, hleft]

end BinaryAlternatingFour


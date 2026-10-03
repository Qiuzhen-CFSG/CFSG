module

public import Theory.LinearAlgebra.BinarySymplecticSevenCertificate

/-!
The finite symplectic certificate is translated to the ordinary matrix API.
Every binary row has a four-bit code, and a symplectic actor with seventh power
one has fourth power equal to its inverse cube. Applying the checked row
certificate therefore forces the actor to be the identity.
-/

public section

open Matrix

namespace BinarySymplecticSeven

set_option synthInstance.maxSize 10000 in
theorem row_certificate : ∀ aa bb cc dd : ZMod 2,
    ∃ code : Fin 16, ∀ index : Fin 4, row code index = ![aa, bb, cc, dd] index := by
  decide

theorem row_surjective : Function.Surjective row := by
  intro vector
  obtain ⟨code, hcode⟩ := row_certificate (vector 0) (vector 1) (vector 2) (vector 3)
  refine ⟨code, ?_⟩
  funext index
  have hentry := hcode index
  fin_cases index <;> exact hentry

theorem decode_surjective (actor : Mat) :
    ∃ aa bb cc dd : Fin 16, decode aa bb cc dd = actor := by
  obtain ⟨aa, haa⟩ := row_surjective (actor 0)
  obtain ⟨bb, hbb⟩ := row_surjective (actor 1)
  obtain ⟨cc, hcc⟩ := row_surjective (actor 2)
  obtain ⟨dd, hdd⟩ := row_surjective (actor 3)
  refine ⟨aa, bb, cc, dd, ?_⟩
  funext index
  fin_cases index
  · exact haa
  · exact hbb
  · exact hcc
  · exact hdd

theorem pairing_eq_mul (actor : Mat) (ii jj : Fin 4) :
    pairing (actor ii) (actor jj) = (actor * J4 * actor.transpose) ii jj := by
  simp [pairing, Matrix.mul_apply, Fin.sum_univ_succ, J4]
  ring


theorem fastMul_eq (left right : Mat) : fastMul left right = left * right := by
  ext ii jj
  simp [fastMul, Matrix.mul_apply, Fin.sum_univ_succ, add_assoc]

theorem swap_eq (actor : Mat) :
    (fun ii jj => actor (swap jj) (swap ii)) = J4 * actor.transpose * J4 := by
  ext ii jj
  fin_cases ii <;> fin_cases jj <;>
    simp [swap, J4, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem J4_square : J4 * J4 = 1 := by decide

theorem rows_preserve (actor : Mat)
    (hpres : actor.transpose * J4 * actor = J4) :
    actor * J4 * actor.transpose = J4 := by
  have hleft : (J4 * actor.transpose * J4) * actor = 1 := by
    calc
      _ = J4 * (actor.transpose * J4 * actor) := by simp only [mul_assoc]
      _ = 1 := by rw [hpres, J4_square]
  have hright : actor * (J4 * actor.transpose * J4) = 1 :=
    mul_eq_one_comm.mp hleft
  calc
    _ = (actor * (J4 * actor.transpose * J4)) * J4 := by
      simp only [mul_assoc, J4_square, mul_one]
    _ = J4 := by rw [hright, one_mul]

theorem power_preserves (actor : Mat)
    (hpres : actor.transpose * J4 * actor = J4) (power : ℕ) :
    (actor ^ power).transpose * J4 * actor ^ power = J4 := by
  induction power with
  | zero => simp
  | succ power ih =>
    rw [pow_succ, transpose_mul]
    calc
      _ = actor.transpose * ((actor ^ power).transpose * J4 * actor ^ power) *
          actor := by simp only [mul_assoc]
      _ = J4 := by rw [ih, hpres]

theorem fourth_eq_inverse_cube (actor : Mat)
    (hpres : actor.transpose * J4 * actor = J4) (hpower : actor ^ 7 = 1) :
    (actor * actor) * (actor * actor) =
      J4 * ((actor * actor) * actor).transpose * J4 := by
  have hcube := power_preserves actor hpres 3
  have hleft : (J4 * (actor ^ 3).transpose * J4) * actor ^ 3 = 1 := by
    calc
      _ = J4 * ((actor ^ 3).transpose * J4 * actor ^ 3) := by
        simp only [mul_assoc]
      _ = 1 := by rw [hcube, J4_square]
  have hseven : actor ^ 3 * actor ^ 4 = 1 := by
    rw [← pow_add]
    exact hpower
  have heq : actor ^ 4 = J4 * (actor ^ 3).transpose * J4 := by
    calc
      _ = ((J4 * (actor ^ 3).transpose * J4) * actor ^ 3) * actor ^ 4 := by
        rw [hleft, one_mul]
      _ = J4 * (actor ^ 3).transpose * J4 := by
        rw [mul_assoc, hseven, mul_one]
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using heq

theorem matrix_order_seven_eq_one
    (actor : Mat) (hpower : actor ^ 7 = 1)
    (hpres : actor.transpose * J4 * actor = J4) : actor = 1 := by
  obtain ⟨aa, bb, cc, dd, rfl⟩ := decode_surjective actor
  have hrows := rows_preserve _ hpres
  have hp (ii jj : Fin 4) :
      pairing (decode aa bb cc dd ii) (decode aa bb cc dd jj) = J4 ii jj := by
    rw [pairing_eq_mul, hrows]
  apply Matrix.ext
  apply certificate aa bb (by simpa [decode, J4] using hp 0 1)
    cc (by simpa [decode, J4] using hp 0 2) (by simpa [decode, J4] using hp 1 2)
    dd (by simpa [decode, J4] using hp 0 3) (by simpa [decode, J4] using hp 1 3)
      (by simpa [decode, J4] using hp 2 3)
  have heq : fourth (decode aa bb cc dd) = inverseCube (decode aa bb cc dd) := by
    unfold fourth inverseCube
    simp only [fastMul_eq, swap_eq]
    exact fourth_eq_inverse_cube _ hpres hpower
  intro ii jj
  exact congr_fun (congr_fun heq ii) jj

end BinarySymplecticSeven

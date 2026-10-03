module

public import Stellmacher.Recognition.FongWreathedCoordinates

/-!
# The internal conjugacy table for Fong's wreathed group

Every element of a height-two wreathed presentation is conjugate inside the
group to one of the fourteen representatives in Fong's table (4), including
the identity. This holds for every presentation, independently of any ambient
fusion or orientation choice.

The proof collects products in the 32 normal forms `s^i*t^j*z^b`. Explicit
conjugators reduce each normal form to the table; each certificate is checked
using the defining relations and congruences modulo four and two. The final
coordinate calculation expresses the table in terms of `F,E,X,J`.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)* (1967), p. 69, table (4), case IIb with parameter zero.
-/

namespace Stellmacher.Recognition.FongWreathedIntrinsic
open ABG.Wreathed
variable {S : Type*} [Group S] (P : Presentation S 2)
private def ev (i j b : ℕ) : S := P.s ^ i * P.t ^ j * P.z ^ b
private theorem ev_mul_zero (i j k l b : ℕ) :
    ev P i j 0 * ev P k l b = ev P (i+k) (j+l) b := by
  dsimp [ev]
  simp only [pow_zero, mul_one, pow_add]
  have hst : Commute P.s P.t := P.commute
  have hc : Commute (P.t ^ j) (P.s ^ k) := hst.symm.pow_pow j k
  calc
    _ = P.s ^ i * (P.t ^ j * P.s ^ k) * P.t ^ l * P.z ^ b := by group
    _ = _ := by rw [hc.eq]; group
private theorem ev_mul_one (i j k l b : ℕ) :
    ev P i j 1 * ev P k l b = ev P (i+l) (j+k) (1+b) := by
  dsimp [ev]
  simp only [pow_one, pow_add]
  have hst : Commute P.s P.t := P.commute
  have hc : Commute (P.t ^ (j+k)) (P.s ^ l) := hst.symm.pow_pow (j+k) l
  calc
    _ = P.s ^ i * P.t ^ j * (P.z * P.s ^ k) * P.t ^ l * P.z ^ b := by group
    _ = P.s ^ i * P.t ^ (j+k) * (P.z * P.t ^ l) * P.z ^ b := by rw [P.z_mul_s_pow, pow_add]; group
    _ = P.s ^ i * (P.t ^ (j+k) * P.s ^ l) * P.z * P.z ^ b := by rw [P.z_mul_t_pow]; group
    _ = _ := by rw [hc.eq, pow_add]; group
private theorem ev_mod (i j b : ℕ) :
    ev P i j b = ev P (i % 4) (j % 4) (b % 2) := by
  dsimp [ev]
  rw [pow_eq_pow_mod i P.s_pow, pow_eq_pow_mod j P.t_pow, pow_eq_pow_mod b P.z_sq]
  rfl

private def reps : Fin 14 → S :=
  ![ev P 0 0 0, ev P 2 2 0, ev P 2 0 0, ev P 1 1 0,
    ev P 3 3 0, ev P 3 1 0, ev P 1 0 1, ev P 2 1 1,
    ev P 1 0 0, ev P 3 2 0, ev P 3 0 0, ev P 1 2 0,
    ev P 2 0 1, ev P 1 3 1]
private theorem conj_ev (i j b k l c a d e : ℕ)
    (h : ev P k l c * ev P i j b = ev P a d e * ev P k l c) :
    IsConj (ev P i j b) (ev P a d e) := by
  exact isConj_iff.mpr ⟨ev P k l c, (mul_inv_eq_iff_eq_mul).mpr h⟩

private theorem ev_eq_of_mod (i j b k l c : ℕ)
    (h : i % 4 = k % 4 ∧ j % 4 = l % 4 ∧ b % 2 = c % 2) :
    ev P i j b = ev P k l c := by
  calc
    _ = ev P (i % 4) (j % 4) (b % 2) := ev_mod P i j b
    _ = ev P (k % 4) (l % 4) (c % 2) := by rw [h.1, h.2.1, h.2.2]
    _ = ev P k l c := (ev_mod P k l c).symm

private theorem table (x : S) : ∃ k : Fin 14, IsConj x (reps P k) := by
  obtain ⟨i, j, b, rfl⟩ := P.exists_normal_form x
  fin_cases i <;> fin_cases j <;> fin_cases b
  · refine ⟨0, ?_⟩
    change IsConj (ev P 0 0 0) (ev P 0 0 0)
    apply conj_ev P 0 0 0 0 0 0
    simp only [ev_mul_zero]
  · refine ⟨13, ?_⟩
    change IsConj (ev P 0 0 1) (ev P 1 3 1)
    apply conj_ev P 0 0 1 0 3 0
    simp only [ev_mul_zero, ev_mul_one]
    apply ev_eq_of_mod
    decide
  · refine ⟨8, ?_⟩
    change IsConj (ev P 0 1 0) (ev P 1 0 0)
    apply conj_ev P 0 1 0 0 0 1
    simp only [ev_mul_zero, ev_mul_one]
  · refine ⟨6, ?_⟩
    change IsConj (ev P 0 1 1) (ev P 1 0 1)
    apply conj_ev P 0 1 1 0 0 1
    simp only [ev_mul_one]
  · refine ⟨2, ?_⟩
    change IsConj (ev P 0 2 0) (ev P 2 0 0)
    apply conj_ev P 0 2 0 0 0 1
    simp only [ev_mul_zero, ev_mul_one]
  · refine ⟨12, ?_⟩
    change IsConj (ev P 0 2 1) (ev P 2 0 1)
    apply conj_ev P 0 2 1 0 0 1
    simp only [ev_mul_one]
  · refine ⟨10, ?_⟩
    change IsConj (ev P 0 3 0) (ev P 3 0 0)
    apply conj_ev P 0 3 0 0 0 1
    simp only [ev_mul_zero, ev_mul_one]
  · refine ⟨7, ?_⟩
    change IsConj (ev P 0 3 1) (ev P 2 1 1)
    apply conj_ev P 0 3 1 0 1 1
    simp only [ev_mul_one]
  · refine ⟨8, ?_⟩
    change IsConj (ev P 1 0 0) (ev P 1 0 0)
    apply conj_ev P 1 0 0 0 0 0
    simp only [ev_mul_zero]
  · refine ⟨6, ?_⟩
    change IsConj (ev P 1 0 1) (ev P 1 0 1)
    apply conj_ev P 1 0 1 0 0 0
    simp only [ev_mul_zero, ev_mul_one]
  · refine ⟨3, ?_⟩
    change IsConj (ev P 1 1 0) (ev P 1 1 0)
    apply conj_ev P 1 1 0 0 0 0
    simp only [ev_mul_zero]
  · refine ⟨12, ?_⟩
    change IsConj (ev P 1 1 1) (ev P 2 0 1)
    apply conj_ev P 1 1 1 0 3 0
    simp only [ev_mul_zero, ev_mul_one]
    apply ev_eq_of_mod
    decide
  · refine ⟨11, ?_⟩
    change IsConj (ev P 1 2 0) (ev P 1 2 0)
    apply conj_ev P 1 2 0 0 0 0
    simp only [ev_mul_zero]
  · refine ⟨7, ?_⟩
    change IsConj (ev P 1 2 1) (ev P 2 1 1)
    apply conj_ev P 1 2 1 0 0 1
    simp only [ev_mul_one]
  · refine ⟨5, ?_⟩
    change IsConj (ev P 1 3 0) (ev P 3 1 0)
    apply conj_ev P 1 3 0 0 0 1
    simp only [ev_mul_zero, ev_mul_one]
  · refine ⟨13, ?_⟩
    change IsConj (ev P 1 3 1) (ev P 1 3 1)
    apply conj_ev P 1 3 1 0 0 0
    simp only [ev_mul_zero, ev_mul_one]
  · refine ⟨2, ?_⟩
    change IsConj (ev P 2 0 0) (ev P 2 0 0)
    apply conj_ev P 2 0 0 0 0 0
    simp only [ev_mul_zero]
  · refine ⟨12, ?_⟩
    change IsConj (ev P 2 0 1) (ev P 2 0 1)
    apply conj_ev P 2 0 1 0 0 0
    simp only [ev_mul_zero, ev_mul_one]
  · refine ⟨11, ?_⟩
    change IsConj (ev P 2 1 0) (ev P 1 2 0)
    apply conj_ev P 2 1 0 0 0 1
    simp only [ev_mul_zero, ev_mul_one]
  · refine ⟨7, ?_⟩
    change IsConj (ev P 2 1 1) (ev P 2 1 1)
    apply conj_ev P 2 1 1 0 0 0
    simp only [ev_mul_zero, ev_mul_one]
  · refine ⟨1, ?_⟩
    change IsConj (ev P 2 2 0) (ev P 2 2 0)
    apply conj_ev P 2 2 0 0 0 0
    simp only [ev_mul_zero]
  · refine ⟨13, ?_⟩
    change IsConj (ev P 2 2 1) (ev P 1 3 1)
    apply conj_ev P 2 2 1 0 1 0
    simp only [ev_mul_zero, ev_mul_one]
  · refine ⟨9, ?_⟩
    change IsConj (ev P 2 3 0) (ev P 3 2 0)
    apply conj_ev P 2 3 0 0 0 1
    simp only [ev_mul_zero, ev_mul_one]
  · refine ⟨6, ?_⟩
    change IsConj (ev P 2 3 1) (ev P 1 0 1)
    apply conj_ev P 2 3 1 0 1 0
    simp only [ev_mul_zero, ev_mul_one]
    apply ev_eq_of_mod
    decide
  · refine ⟨10, ?_⟩
    change IsConj (ev P 3 0 0) (ev P 3 0 0)
    apply conj_ev P 3 0 0 0 0 0
    simp only [ev_mul_zero]
  · refine ⟨7, ?_⟩
    change IsConj (ev P 3 0 1) (ev P 2 1 1)
    apply conj_ev P 3 0 1 0 1 0
    simp only [ev_mul_zero, ev_mul_one]
  · refine ⟨5, ?_⟩
    change IsConj (ev P 3 1 0) (ev P 3 1 0)
    apply conj_ev P 3 1 0 0 0 0
    simp only [ev_mul_zero]
  · refine ⟨13, ?_⟩
    change IsConj (ev P 3 1 1) (ev P 1 3 1)
    apply conj_ev P 3 1 1 0 0 1
    simp only [ev_mul_one]
  · refine ⟨9, ?_⟩
    change IsConj (ev P 3 2 0) (ev P 3 2 0)
    apply conj_ev P 3 2 0 0 0 0
    simp only [ev_mul_zero]
  · refine ⟨6, ?_⟩
    change IsConj (ev P 3 2 1) (ev P 1 0 1)
    apply conj_ev P 3 2 1 0 1 1
    simp only [ev_mul_one]
    apply ev_eq_of_mod
    decide
  · refine ⟨4, ?_⟩
    change IsConj (ev P 3 3 0) (ev P 3 3 0)
    apply conj_ev P 3 3 0 0 0 0
    simp only [ev_mul_zero]
  · refine ⟨12, ?_⟩
    change IsConj (ev P 3 3 1) (ev P 2 0 1)
    apply conj_ev P 3 3 1 0 1 0
    simp only [ev_mul_zero, ev_mul_one]
    apply ev_eq_of_mod
    decide

/-- Fong's internal table, including the identity at index zero. -/
@[expose] public def sylowRepresentative : Fin 14 → S :=
  ![1, J P, X P, F P ^ 2, (F P ^ 2)⁻¹, X P * F P ^ 2,
    F P, F P ^ 3, E P, E P * J P, E P * X P, E P * X P * J P,
    E P * F P, E P * (F P)⁻¹]

private theorem reps_eq (i : Fin 14) : reps P i = sylowRepresentative P i := by
  have he : E P = ev P 1 0 0 := by simp [ev, E]
  have hf : F P = ev P 1 0 1 := by simp [ev, F]
  have hx : X P = ev P 2 0 0 := by simp [ev, X]
  have hf2 : F P ^ 2 = ev P 1 1 0 := by simp [F_sq, ev, Presentation.u]
  have hc : Commute P.s P.t := P.commute
  have hj : J P = ev P 2 2 0 := by simpa [J, Presentation.u, ev] using hc.mul_pow 2
  have hf3 : F P ^ 3 = ev P 2 1 1 := by
    rw [show 3 = 2+1 from rfl, pow_succ, hf2, hf, ev_mul_zero]
  have hf2i : (F P ^ 2)⁻¹ = ev P 3 3 0 := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [hf2, ev_mul_zero, ev_mod]
    simp [ev]
  have hfi : (F P)⁻¹ = ev P 0 3 1 := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [hf, ev_mul_one, ev_mod]
    simp [ev]
  fin_cases i
  · change ev P 0 0 0 = 1
    simp [ev]
  · exact hj.symm
  · exact hx.symm
  · exact hf2.symm
  · exact hf2i.symm
  · change ev P 3 1 0 = X P * F P ^ 2
    rw [hx, hf2, ev_mul_zero]
  · exact hf.symm
  · exact hf3.symm
  · exact he.symm
  · change ev P 3 2 0 = E P * J P
    rw [he, hj, ev_mul_zero]
  · change ev P 3 0 0 = E P * X P
    rw [he, hx, ev_mul_zero]
  · change ev P 1 2 0 = E P * X P * J P
    rw [he, hx, hj, ev_mul_zero, ev_mul_zero]
    exact ev_eq_of_mod P _ _ _ _ _ _ (by decide)
  · change ev P 2 0 1 = E P * F P
    rw [he, hf, ev_mul_zero]
  · change ev P 1 3 1 = E P * (F P)⁻¹
    rw [he, hfi, ev_mul_zero]

/-- Every element is conjugate to an entry of the internal table. -/
public theorem sylowRepresentative_covers (x : S) :
    ∃ i : Fin 14, IsConj x (sylowRepresentative P i) := by
  obtain ⟨i, hi⟩ := table P x
  exact ⟨i, (reps_eq P i) ▸ hi⟩

end Stellmacher.Recognition.FongWreathedIntrinsic

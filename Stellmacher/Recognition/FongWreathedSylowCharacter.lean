module
public import Stellmacher.Recognition.FongWreathedFusionTable
public import Theory.Character.AbelianLinearCharacters

/-!
# Fong's linear character and the full Sylow census

For any height-two wreathed presentation, construct the degree-one character
with `w(F) = I` and `w(E) = -I`. Its value on `s^i t^j z^b` is
`(-I)^i (-I)^j (-1)^b`; uniqueness and multiplication of normal forms prove
that this is a homomorphism on the actual group.

We also refine the certificates of `FongWreathedFusionTable` to an indexed
map from all 32 normal forms to its fourteen representatives. Transport of
the finite sum through `normal_form_bijective` gives their multiplicities.
These two facts supply the full-Sylow restriction calculations without any
ambient fusion hypotheses in this module.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)* (1967), p. 69, table (4), and p. 73, congruence (iii).
-/

noncomputable section
open scoped BigOperators
namespace Stellmacher.Recognition.FongWreathedIntrinsic
namespace RestrictionSums
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

private def tableIndex (v : Fin 4 × Fin 4 × Fin 2) : Fin 14 :=
  ![![![0, 13], ![8, 6], ![2, 12], ![10, 7]],
    ![![8, 6], ![3, 12], ![11, 7], ![5, 13]],
    ![![2, 12], ![11, 7], ![1, 13], ![9, 6]],
    ![![10, 7], ![5, 13], ![9, 6], ![4, 12]]] v.1 v.2.1 v.2.2

private theorem table (v : Fin 4 × Fin 4 × Fin 2) :
    IsConj (P.normalForm v) (reps P (tableIndex v)) := by
  rcases v with ⟨i, j, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases b
  · change IsConj (ev P 0 0 0) (ev P 0 0 0)
    apply conj_ev P 0 0 0 0 0 0
    simp only [ev_mul_zero]
  · change IsConj (ev P 0 0 1) (ev P 1 3 1)
    apply conj_ev P 0 0 1 0 3 0
    simp only [ev_mul_zero, ev_mul_one]
    apply ev_eq_of_mod
    decide
  · change IsConj (ev P 0 1 0) (ev P 1 0 0)
    apply conj_ev P 0 1 0 0 0 1
    simp only [ev_mul_zero, ev_mul_one]
  · change IsConj (ev P 0 1 1) (ev P 1 0 1)
    apply conj_ev P 0 1 1 0 0 1
    simp only [ev_mul_one]
  · change IsConj (ev P 0 2 0) (ev P 2 0 0)
    apply conj_ev P 0 2 0 0 0 1
    simp only [ev_mul_zero, ev_mul_one]
  · change IsConj (ev P 0 2 1) (ev P 2 0 1)
    apply conj_ev P 0 2 1 0 0 1
    simp only [ev_mul_one]
  · change IsConj (ev P 0 3 0) (ev P 3 0 0)
    apply conj_ev P 0 3 0 0 0 1
    simp only [ev_mul_zero, ev_mul_one]
  · change IsConj (ev P 0 3 1) (ev P 2 1 1)
    apply conj_ev P 0 3 1 0 1 1
    simp only [ev_mul_one]
  · change IsConj (ev P 1 0 0) (ev P 1 0 0)
    apply conj_ev P 1 0 0 0 0 0
    simp only [ev_mul_zero]
  · change IsConj (ev P 1 0 1) (ev P 1 0 1)
    apply conj_ev P 1 0 1 0 0 0
    simp only [ev_mul_zero, ev_mul_one]
  · change IsConj (ev P 1 1 0) (ev P 1 1 0)
    apply conj_ev P 1 1 0 0 0 0
    simp only [ev_mul_zero]
  · change IsConj (ev P 1 1 1) (ev P 2 0 1)
    apply conj_ev P 1 1 1 0 3 0
    simp only [ev_mul_zero, ev_mul_one]
    apply ev_eq_of_mod
    decide
  · change IsConj (ev P 1 2 0) (ev P 1 2 0)
    apply conj_ev P 1 2 0 0 0 0
    simp only [ev_mul_zero]
  · change IsConj (ev P 1 2 1) (ev P 2 1 1)
    apply conj_ev P 1 2 1 0 0 1
    simp only [ev_mul_one]
  · change IsConj (ev P 1 3 0) (ev P 3 1 0)
    apply conj_ev P 1 3 0 0 0 1
    simp only [ev_mul_zero, ev_mul_one]
  · change IsConj (ev P 1 3 1) (ev P 1 3 1)
    apply conj_ev P 1 3 1 0 0 0
    simp only [ev_mul_zero, ev_mul_one]
  · change IsConj (ev P 2 0 0) (ev P 2 0 0)
    apply conj_ev P 2 0 0 0 0 0
    simp only [ev_mul_zero]
  · change IsConj (ev P 2 0 1) (ev P 2 0 1)
    apply conj_ev P 2 0 1 0 0 0
    simp only [ev_mul_zero, ev_mul_one]
  · change IsConj (ev P 2 1 0) (ev P 1 2 0)
    apply conj_ev P 2 1 0 0 0 1
    simp only [ev_mul_zero, ev_mul_one]
  · change IsConj (ev P 2 1 1) (ev P 2 1 1)
    apply conj_ev P 2 1 1 0 0 0
    simp only [ev_mul_zero, ev_mul_one]
  · change IsConj (ev P 2 2 0) (ev P 2 2 0)
    apply conj_ev P 2 2 0 0 0 0
    simp only [ev_mul_zero]
  · change IsConj (ev P 2 2 1) (ev P 1 3 1)
    apply conj_ev P 2 2 1 0 1 0
    simp only [ev_mul_zero, ev_mul_one]
  · change IsConj (ev P 2 3 0) (ev P 3 2 0)
    apply conj_ev P 2 3 0 0 0 1
    simp only [ev_mul_zero, ev_mul_one]
  · change IsConj (ev P 2 3 1) (ev P 1 0 1)
    apply conj_ev P 2 3 1 0 1 0
    simp only [ev_mul_zero, ev_mul_one]
    apply ev_eq_of_mod
    decide
  · change IsConj (ev P 3 0 0) (ev P 3 0 0)
    apply conj_ev P 3 0 0 0 0 0
    simp only [ev_mul_zero]
  · change IsConj (ev P 3 0 1) (ev P 2 1 1)
    apply conj_ev P 3 0 1 0 1 0
    simp only [ev_mul_zero, ev_mul_one]
  · change IsConj (ev P 3 1 0) (ev P 3 1 0)
    apply conj_ev P 3 1 0 0 0 0
    simp only [ev_mul_zero]
  · change IsConj (ev P 3 1 1) (ev P 1 3 1)
    apply conj_ev P 3 1 1 0 0 1
    simp only [ev_mul_one]
  · change IsConj (ev P 3 2 0) (ev P 3 2 0)
    apply conj_ev P 3 2 0 0 0 0
    simp only [ev_mul_zero]
  · change IsConj (ev P 3 2 1) (ev P 1 0 1)
    apply conj_ev P 3 2 1 0 1 1
    simp only [ev_mul_one]
    apply ev_eq_of_mod
    decide
  · change IsConj (ev P 3 3 0) (ev P 3 3 0)
    apply conj_ev P 3 3 0 0 0 0
    simp only [ev_mul_zero]
  · change IsConj (ev P 3 3 1) (ev P 2 0 1)
    apply conj_ev P 3 3 1 0 1 0
    simp only [ev_mul_zero, ev_mul_one]
    apply ev_eq_of_mod
    decide

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


private theorem class_eq {H : Type*} [Group H] {φ : H → ℂ}
    (hφ : IsClassFunction φ) {x y : H} (h : IsConj x y) : φ x = φ y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (hφ x g).symm

attribute [local instance] Fintype.ofFinite

/-- The sum of a class function over the wreathed group, with the fourteen
internal class multiplicities made explicit. -/
public theorem sum_table [Finite S] (φ : S → ℂ) (hφ : IsClassFunction φ) :
    ∑ x : S, φ x = ∑ i : Fin 14,
      (![1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 2, 2, 4, 4] i : ℂ) *
        φ (sylowRepresentative P i) := by
  classical
  rw [← Fintype.sum_bijective P.normalForm P.normal_form_bijective
    (fun v => φ (sylowRepresentative P (tableIndex v))) φ
    (fun v => (class_eq hφ ((reps_eq P _) ▸ table P v)).symm)]
  change (∑ v : Fin 4 × Fin 4 × Fin 2, φ (sylowRepresentative P (tableIndex v))) = _
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.sum_univ_zero,
    tableIndex, sylowRepresentative, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val]
  ring

private def normalEquiv : (Fin 4 × Fin 4 × Fin 2) ≃ S :=
  Equiv.ofBijective P.normalForm P.normal_form_bijective

private def linearValue (x : S) : ℂ :=
  let v := (normalEquiv P).symm x
  (-Complex.I) ^ v.1.val * (-Complex.I) ^ v.2.1.val * (-1) ^ v.2.2.val

private theorem linearValue_ev (i j b : ℕ) :
    linearValue P (ev P i j b) = (-Complex.I) ^ i * (-Complex.I) ^ j * (-1) ^ b := by
  have hn : ev P (i % 4) (j % 4) (b % 2) =
      normalEquiv P (⟨i % 4, Nat.mod_lt _ (by decide)⟩,
        ⟨j % 4, Nat.mod_lt _ (by decide)⟩, ⟨b % 2, Nat.mod_lt _ (by decide)⟩) := rfl
  rw [ev_mod, hn]
  simp only [linearValue, Equiv.symm_apply_apply]
  have hi : (-Complex.I) ^ 4 = 1 := by norm_num [pow_succ, Complex.I_mul_I]
  have hm : (-1 : ℂ) ^ 2 = 1 := by norm_num
  rw [← pow_eq_pow_mod i hi, ← pow_eq_pow_mod j hi, ← pow_eq_pow_mod b hm]

/-- Fong's degree-one character, constructed on the actual presentation. -/
public def w : S →* ℂ where
  toFun := linearValue P
  map_one' := by
    have h := linearValue_ev P 0 0 0
    simpa [ev] using h
  map_mul' x y := by
    obtain ⟨i, j, b, rfl⟩ := P.exists_normal_form x
    obtain ⟨k, l, c, rfl⟩ := P.exists_normal_form y
    change linearValue P (ev P i.val j.val b.val * ev P k.val l.val c.val) =
      linearValue P (ev P i.val j.val b.val) * linearValue P (ev P k.val l.val c.val)
    fin_cases b <;> simp only [ev_mul_zero, ev_mul_one,
      linearValue_ev, pow_add, pow_zero, pow_one] <;> ring

private theorem w_ev (i j b : ℕ) :
    w P (ev P i j b) = (-Complex.I) ^ i * (-Complex.I) ^ j * (-1) ^ b :=
  linearValue_ev P i j b

public theorem w_E : w P (E P) = -Complex.I := by
  have h := w_ev P 1 0 0
  simpa [ev, E] using h

public theorem w_F : w P (F P) = Complex.I := by
  have h := w_ev P 1 0 1
  simpa [ev, F] using h

public theorem w_isLinearCharacter : IsLinearCharacter (w P : S → ℂ) :=
  (w P).isLinearCharacter

private theorem w_X : w P (X P) = -1 := by
  rw [← E_sq, map_pow, w_E]
  norm_num

private theorem w_J : w P (J P) = 1 := by
  rw [← F_four, map_pow, w_F]
  norm_num [pow_succ, Complex.I_mul_I]


/-- Values of Fong's linear character on the internal representatives. -/
public theorem w_table (i : Fin 14) : w P (sylowRepresentative P i) =
    ![1, 1, -1, -1, -1, 1, Complex.I, -Complex.I, -Complex.I, -Complex.I,
      Complex.I, Complex.I, 1, -1] i := by
  fin_cases i <;> simp [sylowRepresentative, map_mul, map_inv,
    w_E, w_F, w_X, w_J, pow_succ, Complex.I_mul_I]

end RestrictionSums
end Stellmacher.Recognition.FongWreathedIntrinsic

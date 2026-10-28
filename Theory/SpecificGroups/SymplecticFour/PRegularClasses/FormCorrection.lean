module

public import Theory.SpecificGroups.SymplecticFour.PRegularClasses.FormCorrection.Quadratic
public import Theory.SpecificGroups.SymplecticFour.PRegularClasses.FormCorrection.OddAverage
public import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Correcting a general-linear intertwiner to a symplectic conjugator

Over a finite field of characteristic two, two odd-order symplectic matrices
which are conjugate in GL are conjugate in the actual symplectic group.
For an intertwiner D, pull the standard form back to B = DᵀJD. Its ratio T = JB
commutes with g and satisfies a quadratic relation. A nonzero linear coefficient
gives a polynomial square root S of T, with SᵀJS = B. In the other case,
T = aI + N with N² = 0. A linear half of JN, averaged over the odd cyclic group,
constructs S directly. The vanishing N² kills the quadratic error term.
Finally D S⁻¹ preserves J and still intertwines g and h.

This argument covers all repeated factors and the fixed symplectic summand
without any invariant-form classification assumption. It does not assume that
the ratio T has odd order. Mathlib's transpose-first membership criterion is
used to construct the conjugator in `Matrix.symplecticGroup`.

Source context: GLS III, 2.8.2, 2.8.6(a), Examples 2.8.10(d),
`refs/KGroup/GLS3/chapter2.tex`; Aschbacher--Smith, `refs/quasithin.pdf`,
proof of G.9.3, printed pp.356--357. This is the form-correction input to the
independent characteristic-polynomial class-counting argument.
-/

namespace Theory.SpecificGroups.SymplecticFour.PRegularClasses.FormCorrection
open Matrix
variable {F : Type*} [Field F] [CharP F 2]
local notation "M" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F
local notation "J₄" => Matrix.J (Fin 2) F
local notation "Sp" => Matrix.symplecticGroup (Fin 2) F

local instance : CharP M 2 :=
  charP_of_injective_algebraMap (algebraMap F M).injective 2

private theorem j_sq : J₄ * J₄ = (1 : M) := by
  rw [Matrix.J_squared, CharTwo.neg_eq]

private theorem j_alt : (J₄ : M).toBilin'.IsAlt := by
  intro x
  simp [Matrix.toBilin'_apply, Matrix.J, Matrix.fromBlocks, Matrix.one_apply,
    Fintype.sum_sum_type, Fin.sum_univ_two, CharTwo.neg_eq]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

private theorem alt_symm (A : M) (hA : A.toBilin'.IsAlt) : A.transpose = A := by
  ext i j
  have h := hA.neg_eq (Pi.single i 1) (Pi.single j 1)
  simpa only [Matrix.toBilin'_single, CharTwo.neg_eq, transpose_apply] using h.symm

omit [CharP F 2] in
private theorem linear_adj (T : M) (hT : T.transpose * J₄ = J₄ * T) (u v : F) :
    (u • T + v • (1 : M)).transpose * J₄ = J₄ * (u • T + v • (1 : M)) := by
  simp [transpose_add, transpose_smul, add_mul, mul_add, hT]

omit [CharP F 2] in
private theorem nilpotent_gram (X : M) (hXX : X.transpose * J₄ * X = 0)
    (b : F) (hb : b ≠ 0) :
    (b • (1 : M) + b⁻¹ • X).transpose * J₄ * (b • (1 : M) + b⁻¹ • X) =
      b ^ 2 • J₄ + (X.transpose * J₄ + J₄ * X) := by
  simp only [transpose_add, transpose_smul, transpose_one, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, one_mul, mul_one]
  rw [← pow_two, mul_inv_cancel₀ hb, inv_mul_cancel₀ hb, one_smul, one_smul]
  rw [hXX, smul_zero, add_zero]
  abel

variable [Finite F]

private theorem exists_gram_factor (g : Sp) (hg : ¬ 2 ∣ orderOf g)
    (B : M) (hB : B.toBilin'.IsAlt) (hu : IsUnit B)
    (hBinv : g.val.transpose * B * g.val = B) :
    ∃ S : M, IsUnit S ∧ Commute S g.val ∧ S.transpose * J₄ * S = B := by
  let T : M := J₄ * B
  have hJT : J₄ * T = B := by simp only [T, ← mul_assoc, j_sq, one_mul]
  have hTadj : T.transpose * J₄ = J₄ * T := by
    simp only [T, transpose_mul, Matrix.J_transpose, CharTwo.neg_eq,
      alt_symm B hB, mul_assoc, j_sq, mul_one]
    rw [← mul_assoc, j_sq, one_mul]
  have hTu : IsUnit T :=
    ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_J _ _)).mul hu
  have hgJ : g.val * J₄ * g.val.transpose = J₄ := SymplecticGroup.mem_iff.mp g.property
  have hTg : Commute T g.val := by
    change T * g.val = g.val * T
    calc
      T * g.val = (g.val * J₄ * g.val.transpose) * B * g.val := by rw [hgJ]
      _ = g.val * (J₄ * (g.val.transpose * B * g.val)) := by simp only [mul_assoc]
      _ = g.val * T := by rw [hBinv]
  obtain ⟨c, d, hq⟩ := ratio_quadratic B hB
  change T ^ 2 + c • T + d • (1 : M) = 0 at hq
  by_cases hc : c = 0
  · rw [hc, zero_smul, add_zero] at hq
    have hT2 : T ^ 2 = d • (1 : M) := CharTwo.add_eq_zero.mp hq
    obtain ⟨a, ha⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := F)) d
    change a ^ 2 = d at ha
    have ha0 : a ≠ 0 := by
      intro hz
      have hzero : T ^ 2 = 0 := by rw [hT2, ← ha, hz]; simp
      exact (hTu.pow 2).ne_zero hzero
    let N : M := T + a • (1 : M)
    have hN2 : N ^ 2 = 0 := by
      have h := linear_sq T 1 a
      simpa only [one_smul, one_pow, hT2, ha, CharTwo.add_self_eq_zero] using h
    have hNadj : N.transpose * J₄ = J₄ * N := by
      simpa only [one_smul] using linear_adj T hTadj 1 a
    have hNg : Commute N g.val := hTg.add_left ((Commute.one_left _).smul_left a)
    have hJN : J₄ * N = B + a • J₄ := by simp [N, mul_add, hJT]
    have hNalt : (J₄ * N).toBilin'.IsAlt := by
      rw [hJN, map_add, map_smul]
      exact hB.add (j_alt.smul a)
    have hNinv : g.val.transpose * (J₄ * N) * g.val = J₄ * N := by
      calc
        _ = (g.val.transpose * J₄ * g.val) * N := by
          rw [mul_assoc, mul_assoc, hNg.eq]; simp only [mul_assoc]
        _ = _ := by rw [SymplecticGroup.mem_iff'.mp g.property]
    obtain ⟨Z, hZg, hZ⟩ := exists_odd_invariant_half
      (Matrix.symplecticGroup (Fin 2) F).subtype g hg (J₄ * N) hNalt hNinv
    let X : M := N * Z
    have hXg : Commute X g.val := hNg.mul_left hZg
    have hX : X.transpose * J₄ + J₄ * X = J₄ * N := by
      simpa only [X, transpose_mul, mul_assoc, hNadj] using hZ
    have hXX : X.transpose * J₄ * X = 0 := by
      calc
        _ = Z.transpose * (N.transpose * J₄) * N * Z := by simp [X, transpose_mul, mul_assoc]
        _ = Z.transpose * J₄ * (N * N) * Z := by rw [hNadj]; simp only [mul_assoc]
        _ = 0 := by rw [← pow_two, hN2]; simp
    obtain ⟨b, hb⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := F)) a
    change b ^ 2 = a at hb
    have hb0 : b ≠ 0 := by intro hz; apply ha0; rw [← hb, hz]; simp
    let S : M := b • 1 + b⁻¹ • X
    have hS : S.transpose * J₄ * S = B := by
      rw [nilpotent_gram X hXX b hb0, hb, hX, hJN]
      simpa only [add_comm B (a • J₄)] using CharTwo.add_cancel_left (a • J₄) B
    have hSu : IsUnit S := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      have h := (Matrix.isUnit_iff_isUnit_det B).mp hu
      rw [← hS, det_mul, det_mul] at h
      exact isUnit_of_mul_isUnit_right h
    exact ⟨S, hSu, ((Commute.one_left _).smul_left b).add_left (hXg.smul_left b⁻¹), hS⟩
  · obtain ⟨u, v, hS2⟩ := exists_linear_square_root T c d hc hq
    let S : M := u • T + v • 1
    have hSadj := linear_adj T hTadj u v
    refine ⟨S, (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (hS2 ▸ hTu),
      (hTg.smul_left u).add_left ((Commute.one_left _).smul_left v), ?_⟩
    calc
      S.transpose * J₄ * S = J₄ * S ^ 2 := by rw [hSadj, pow_two, mul_assoc]
      _ = B := by rw [hS2, hJT]

private theorem isConj_of_intertwiner (g h : Sp) (hg : ¬ 2 ∣ orderOf g)
    (D : M) (hD : IsUnit D) (hinter : D * g.val = h.val * D) : IsConj g h := by
  let B : M := D.transpose * J₄ * D
  have hB : B.toBilin'.IsAlt := by
    rw [show B = D.transpose * J₄ * D from rfl, ← Matrix.toBilin'_comp]
    intro x
    exact j_alt (D.toLin' x)
  have hBu : IsUnit B :=
    ((Matrix.isUnit_transpose D).mpr hD).mul
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_J _ _)) |>.mul hD
  have hBinv : g.val.transpose * B * g.val = B := by
    calc
      _ = (D * g.val).transpose * J₄ * (D * g.val) := by simp [B, transpose_mul, mul_assoc]
      _ = (h.val * D).transpose * J₄ * (h.val * D) := by rw [hinter]
      _ = D.transpose * (h.val.transpose * J₄ * h.val) * D := by simp only [transpose_mul, mul_assoc]
      _ = B := by rw [SymplecticGroup.mem_iff'.mp h.property]
  obtain ⟨S, hSu, hSg, hS⟩ := exists_gram_factor g hg B hB hBu hBinv
  rcases hSu with ⟨s, rfl⟩
  have hcform : (D * (s⁻¹).val).transpose * J₄ * (D * (s⁻¹).val) = J₄ := by
    calc
      _ = (s⁻¹).val.transpose * B * (s⁻¹).val := by simp only [B, transpose_mul, mul_assoc]
      _ = (s⁻¹).val.transpose * (s.val.transpose * J₄ * s.val) * (s⁻¹).val := by rw [hS]
      _ = (s.val * (s⁻¹).val).transpose * J₄ * (s.val * (s⁻¹).val) := by
        simp only [transpose_mul, mul_assoc]
      _ = J₄ := by simp
  let C : Sp := ⟨D * (s⁻¹).val, SymplecticGroup.mem_iff'.mpr hcform⟩
  have hinterC : C * g = h * C := by
    apply Subtype.ext
    change (D * (s⁻¹).val) * g.val = h.val * (D * (s⁻¹).val)
    rw [mul_assoc, hSg.units_inv_left.eq, ← mul_assoc, hinter, mul_assoc]
  exact isConj_iff.mpr ⟨C, by rw [hinterC]; simp⟩

end Theory.SpecificGroups.SymplecticFour.PRegularClasses.FormCorrection

namespace Theory.SpecificGroups.SymplecticFour.PRegularClasses

/-- An invertible linear intertwiner between odd-order symplectic four-space
matrices can be corrected to a conjugator in the actual symplectic group.
There is no field-size restriction. -/
public theorem isConj_of_unit_intertwiner
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (g h : Matrix.symplecticGroup (Fin 2) F)
    (hg : ¬ 2 ∣ orderOf g) (_hh : ¬ 2 ∣ orderOf h)
    (D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (hD : IsUnit D) (hinter : D * g.val = h.val * D) : IsConj g h :=
  FormCorrection.isConj_of_intertwiner g h hg D hD hinter

end Theory.SpecificGroups.SymplecticFour.PRegularClasses

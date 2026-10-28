module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Theory.SpecificGroups.SL3.InvolutionBlock
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Involutions in the small projective linear groups

The image of the matrix `[0,-1;1,0]` is an involution in PSL₂ over every
field: its square is scalar and it is not scalar. In dimension three and
characteristic different from two, `diag(-1,-1,1)` is a noncentral involution.
Lagrange's theorem then proves even order over finite fields.

These concrete witnesses supply the parity input in Aschbacher--Smith,
*The Classification of Quasithin Groups*, E.1.14(6)--(7), printed p.214.
-/

public section

open scoped MatrixGroups

namespace Matrix
variable (F : Type*) [Field F]

private def projectiveInvolutionLift : SL(2,F) :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

/-- The Weyl matrix has order two modulo the scalar center. -/
theorem ProjectiveSpecialLinearGroup.exists_orderOf_eq_two_fin_two :
    ∃ x : PSL(2,F), orderOf x = 2 := by
  let q := QuotientGroup.mk' (Subgroup.center SL(2,F))
  refine ⟨q (projectiveInvolutionLift F), orderOf_eq_prime ?_ ?_⟩
  · rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
    refine ⟨-1, by simp, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_two]
    change (Matrix.scalar (Fin 2) (-1) : Matrix (Fin 2) (Fin 2) F) =
      !![0, -1; 1, 0] * !![0, -1; 1, 0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
      ((QuotientGroup.eq_one_iff _).mp h)
    have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 1 0) hr
    simp [projectiveInvolutionLift] at hh

/-- In odd characteristic the standard SL₃ involution survives projectivization. -/
theorem SL3.standardInvolution_not_mem_center (h2 : (2 : F) ≠ 0) :
    SL3.standardInvolution F ∉ Subgroup.center SL(3,F) := by
  intro h
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have h₀ := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 0 0) hr
  have h₂ := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 2 2) hr
  simp [SL3.standardInvolution] at h₀ h₂
  apply h2
  linear_combination h₀ - h₂

theorem ProjectiveSpecialLinearGroup.exists_orderOf_eq_two_fin_three
    (h2 : (2 : F) ≠ 0) : ∃ x : PSL(3,F), orderOf x = 2 := by
  let q := QuotientGroup.mk' (Subgroup.center SL(3,F))
  refine ⟨q (SL3.standardInvolution F), orderOf_eq_prime ?_ ?_⟩
  · rw [← map_pow, SL3.standardInvolution_sq, map_one]
  · exact fun h => SL3.standardInvolution_not_mem_center F h2
      ((QuotientGroup.eq_one_iff _).mp h)

theorem ProjectiveSpecialLinearGroup.two_dvd_card_fin_two :
    2 ∣ Nat.card PSL(2,F) := by
  obtain ⟨x, hx⟩ := ProjectiveSpecialLinearGroup.exists_orderOf_eq_two_fin_two F
  simpa only [hx] using orderOf_dvd_natCard x

theorem ProjectiveSpecialLinearGroup.two_dvd_card_fin_three (h2 : (2 : F) ≠ 0) :
    2 ∣ Nat.card PSL(3,F) := by
  obtain ⟨x, hx⟩ := ProjectiveSpecialLinearGroup.exists_orderOf_eq_two_fin_three F h2
  simpa only [hx] using orderOf_dvd_natCard x

end Matrix

/-- Odd cardinality excludes characteristic two, without choosing a field model. -/
theorem Field.two_ne_zero_of_odd_card (F : Type*) [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  intro h2
  have hd := (ringChar.spec F 2).mp h2
  have hc : ringChar F = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (CharP.ringChar_ne_one (R := F))
  let := Fintype.ofFinite F
  have heven := FiniteField.even_card_of_char_two hc
  rw [← Nat.card_eq_fintype_card] at heven
  exact hodd.not_two_dvd_nat (Nat.dvd_of_mod_eq_zero heven)

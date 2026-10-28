module

public import Theory.AlgebraicGroup.RootSystems.IntegralTitsCoherence
public import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basis

/-!
# Scalar compatibility of integral Tits conjugation

This module maps the integral divided-power unipotents to the finite nilpotent exponentials in
Geck's characteristic-zero matrix model.  The exponential adjoint identity then proves that
conjugation by every mapped Tits word preserves the Geck Lie algebra.  This is the Lie-membership
half of the algebraically closed root-space argument.
-/

namespace RootPairing.IntegralGeckConstruction

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι R M N : Type*} [Field R] [CharZero R] [IsAlgClosed R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private lemma map_nsmul_matrix (n : ℕ)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    (n • A).map (algebraMap ℤ R) =
      (n : R) • A.map (algebraMap ℤ R) := by
  let F : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ →+
      Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
    { toFun := fun B => B.map (algebraMap ℤ R)
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp }
  change F (n • A) = (n : R) • F A
  rw [F.map_nsmul]
  exact (Nat.cast_smul_eq_nsmul R n (F A)).symm

private lemma map_zsmul_matrix (z : ℤ)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    (z • A).map (algebraMap ℤ R) =
      (z : R) • A.map (algebraMap ℤ R) := by
  let F : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ →+
      Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
    { toFun := fun B => B.map (algebraMap ℤ R)
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp }
  change F (z • A) = (z : R) • F A
  rw [F.map_zsmul]
  exact (Int.cast_smul_eq_zsmul R z (F A)).symm

private lemma map_intCast_mul_matrix (z : ℤ)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    ((z : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) * A).map
        (algebraMap ℤ R) =
      (z : R) • A.map (algebraMap ℤ R) := by
  rw [Matrix.map_mul, Matrix.map_intCast (map_zero (algebraMap ℤ R))]
  simpa [← smul_eq_diagonal_mul]

private lemma map_intCast_pow_mul_matrix (z : ℤ) (n : ℕ)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    ((z : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) ^ n * A).map
        (algebraMap ℤ R) =
      (z : R) ^ n • A.map (algebraMap ℤ R) := by
  simpa only [Int.cast_pow] using
    (map_intCast_mul_matrix (P := P) (R := R) (b := b) (z := z ^ n) A)

private lemma map_add_matrix
    (A B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    (A + B).map (algebraMap ℤ R) =
      A.map (algebraMap ℤ R) + B.map (algebraMap ℤ R) :=
  Matrix.map_add (algebraMap ℤ R) (map_add (algebraMap ℤ R)) A B

public lemma map_one_matrix :
    (1 : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ).map
        (algebraMap ℤ R) = 1 :=
  Matrix.map_one (algebraMap ℤ R) (map_zero (algebraMap ℤ R))
    (map_one (algebraMap ℤ R))

private lemma map_eUnipotent_formula (i : b.support) (t : ℤ) :
    (eUnipotent i t).map (algebraMap ℤ R) =
      1 + (t : R) • (eDividedPower i 1).map (algebraMap ℤ R) +
        (t : R) ^ 2 • (eDividedPower i 2).map (algebraMap ℤ R) +
          (t : R) ^ 3 • (eDividedPower i 3).map (algebraMap ℤ R) := by
  rw [eUnipotent, map_add_matrix, map_add_matrix, map_add_matrix, map_one_matrix]
  rw [map_zsmul_matrix, map_zsmul_matrix, map_zsmul_matrix]
  norm_num

private lemma map_eDividedPower_two (i : b.support) :
    (eDividedPower i 2).map (algebraMap ℤ R) =
      (2 : R)⁻¹ • RootPairing.GeckConstruction.e i ^ 2 := by
  have h := congrArg (fun A => A.map (algebraMap ℤ R))
    (eMatrix_pow_eq_factorial_smul (P := P) i 2)
  simp only [Matrix.map_pow, map_eMatrix, map_nsmul_matrix] at h
  rw [h]
  simp [smul_smul]

private lemma map_eDividedPower_three (i : b.support) :
    (eDividedPower i 3).map (algebraMap ℤ R) =
      (6 : R)⁻¹ • RootPairing.GeckConstruction.e i ^ 3 := by
  have h := congrArg (fun A => A.map (algebraMap ℤ R))
    (eMatrix_pow_eq_factorial_smul (P := P) i 3)
  simp only [Matrix.map_pow, map_eMatrix, map_nsmul_matrix] at h
  norm_num at h
  rw [h]
  simp [smul_smul]

public lemma map_eUnipotent_eq_exp (i : b.support) (t : ℤ) :
    (eUnipotent i t).map (algebraMap ℤ R) =
      IsNilpotent.exp ((t : R) • RootPairing.GeckConstruction.e i) := by
  have he4 : RootPairing.GeckConstruction.e (P := P) i ^ 4 = 0 := by
    have h := congrArg (fun A => A.map (algebraMap ℤ R))
      (eMatrix_pow_eq_factorial_smul (P := P) i 4)
    rw [eDividedPower_eq_zero_of_four_le i (show 4 ≤ 4 by omega), nsmul_zero] at h
    have hz : (0 : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ).map
        (algebraMap ℤ R) = 0 :=
      Matrix.map_zero (algebraMap ℤ R) (map_zero (algebraMap ℤ R))
    rw [hz] at h
    simpa only [Matrix.map_pow, map_eMatrix] using h
  rw [IsNilpotent.exp_eq_sum (show ((t : R) •
    RootPairing.GeckConstruction.e (P := P) i) ^ 4 = 0 by
      rw [smul_pow, he4, smul_zero])]
  rw [map_eUnipotent_formula]
  simp only [eDividedPower_one, map_eMatrix,
    map_eDividedPower_two, map_eDividedPower_three, Finset.sum_range_succ]
  norm_num
  simp only [smul_pow]
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply]
  simp only [← Rat.cast_smul_eq_qsmul R, smul_eq_mul]
  ring

private lemma map_fDividedPower_two (i : b.support) :
    (fDividedPower i 2).map (algebraMap ℤ R) =
      (2 : R)⁻¹ • RootPairing.GeckConstruction.f i ^ 2 := by
  have h := congrArg (fun A => A.map (algebraMap ℤ R))
    (fMatrix_pow_eq_factorial_smul (P := P) i 2)
  simp only [Matrix.map_pow, map_fMatrix, map_nsmul_matrix] at h
  rw [h]
  simp [smul_smul]

private lemma map_fDividedPower_three (i : b.support) :
    (fDividedPower i 3).map (algebraMap ℤ R) =
      (6 : R)⁻¹ • RootPairing.GeckConstruction.f i ^ 3 := by
  have h := congrArg (fun A => A.map (algebraMap ℤ R))
    (fMatrix_pow_eq_factorial_smul (P := P) i 3)
  simp only [Matrix.map_pow, map_fMatrix, map_nsmul_matrix] at h
  norm_num at h
  rw [h]
  simp [smul_smul]

private lemma map_fUnipotent_formula (i : b.support) (t : ℤ) :
    (fUnipotent i t).map (algebraMap ℤ R) =
      1 + (t : R) • (fDividedPower i 1).map (algebraMap ℤ R) +
        (t : R) ^ 2 • (fDividedPower i 2).map (algebraMap ℤ R) +
          (t : R) ^ 3 • (fDividedPower i 3).map (algebraMap ℤ R) := by
  rw [fUnipotent, map_add_matrix, map_add_matrix, map_add_matrix, map_one_matrix]
  rw [map_zsmul_matrix, map_zsmul_matrix, map_zsmul_matrix]
  norm_num

public lemma map_fUnipotent_eq_exp (i : b.support) (t : ℤ) :
    (fUnipotent i t).map (algebraMap ℤ R) =
      IsNilpotent.exp ((t : R) • RootPairing.GeckConstruction.f i) := by
  have hf4 : RootPairing.GeckConstruction.f (P := P) i ^ 4 = 0 := by
    have h := congrArg (fun A => A.map (algebraMap ℤ R))
      (fMatrix_pow_eq_factorial_smul (P := P) i 4)
    rw [fDividedPower_eq_zero_of_four_le i (show 4 ≤ 4 by omega), nsmul_zero] at h
    have hz : (0 : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ).map
        (algebraMap ℤ R) = 0 :=
      Matrix.map_zero (algebraMap ℤ R) (map_zero (algebraMap ℤ R))
    rw [hz] at h
    simpa only [Matrix.map_pow, map_fMatrix] using h
  rw [IsNilpotent.exp_eq_sum (show ((t : R) •
    RootPairing.GeckConstruction.f (P := P) i) ^ 4 = 0 by
      rw [smul_pow, hf4, smul_zero])]
  rw [map_fUnipotent_formula]
  simp only [fDividedPower_one, map_fMatrix, map_fDividedPower_two,
    map_fDividedPower_three, Finset.sum_range_succ]
  norm_num
  simp only [smul_pow]
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply]
  simp only [← Rat.cast_smul_eq_qsmul R, smul_eq_mul]
  ring

private lemma pow_mulLeft_apply
    (E X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) (n : ℕ) :
    (LinearMap.mulLeft R E ^ n) X = E ^ n * X := by
  induction n generalizing X with
  | zero => simp
  | succ n ih => simp [pow_succ, Module.End.mul_apply, ih, mul_assoc]

private lemma pow_mulRight_apply
    (E X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) (n : ℕ) :
    (LinearMap.mulRight R E ^ n) X = X * E ^ n := by
  induction n generalizing X with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, LinearMap.mulRight_apply, ih]
      rw [mul_assoc, (Commute.self_pow E n).eq]
      rw [pow_succ]

private lemma exp_mulLeft_apply
    {E : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R} (hE : IsNilpotent E)
    (X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :
    IsNilpotent.exp (LinearMap.mulLeft R E) X = IsNilpotent.exp E * X := by
  obtain ⟨n, hn⟩ := hE
  have hL : (LinearMap.mulLeft R E) ^ n = 0 := by
    ext Y
    rw [pow_mulLeft_apply, hn, zero_mul, LinearMap.zero_apply]
  rw [IsNilpotent.exp_eq_sum hL, IsNilpotent.exp_eq_sum hn]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, pow_mulLeft_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [smul_mul_assoc]

private lemma exp_mulRight_apply
    {E : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R} (hE : IsNilpotent E)
    (X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :
    IsNilpotent.exp (LinearMap.mulRight R E) X = X * IsNilpotent.exp E := by
  obtain ⟨n, hn⟩ := hE
  have hR : (LinearMap.mulRight R E) ^ n = 0 := by
    ext Y
    rw [pow_mulRight_apply, hn, mul_zero, LinearMap.zero_apply]
  rw [IsNilpotent.exp_eq_sum hR, IsNilpotent.exp_eq_sum hn]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, pow_mulRight_apply]
  rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Matrix.mul_smul]

public lemma exp_ad_apply
    {E : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R} (hE : IsNilpotent E)
    (X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :
    IsNilpotent.exp ((LieAlgebra.ad R
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)) E) X =
        IsNilpotent.exp E * X * IsNilpotent.exp (-E) := by
  let L : Module.End R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :=
    LinearMap.mulLeft R E
  let Q : Module.End R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :=
    LinearMap.mulRight R E
  have hL : IsNilpotent L := (LinearMap.isNilpotent_mulLeft_iff R E).2 hE
  have hQ : IsNilpotent Q := (LinearMap.isNilpotent_mulRight_iff R E).2 hE
  have hcomm : Commute L (-Q) := by
    rw [commute_iff_eq]
    ext Y
    simp [L, Q, Module.End.mul_apply, mul_assoc]
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  change IsNilpotent.exp (L - Q) X = _
  rw [sub_eq_add_neg, IsNilpotent.exp_add_of_commute hcomm hL hQ.neg]
  change IsNilpotent.exp L (IsNilpotent.exp (-Q) X) = _
  rw [show -Q = LinearMap.mulRight R (-E) by ext Y; simp [Q]]
  rw [exp_mulRight_apply hE.neg, exp_mulLeft_apply hE]
  simp only [mul_assoc]

private lemma exp_conj_mem_lieAlgebra
    {E X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R}
    (hE : IsNilpotent E) (hEmem : E ∈ RootPairing.GeckConstruction.lieAlgebra b)
    (hX : X ∈ RootPairing.GeckConstruction.lieAlgebra b) :
    IsNilpotent.exp E * X * IsNilpotent.exp (-E) ∈
      RootPairing.GeckConstruction.lieAlgebra b := by
  let L := RootPairing.GeckConstruction.lieAlgebra b
  let E' : L := ⟨E, hEmem⟩
  let X' : L := ⟨X, hX⟩
  have hAmbient : IsNilpotent ((LieAlgebra.ad R
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)) E) :=
    LieAlgebra.ad_nilpotent_of_nilpotent hE
  have hRestricted : IsNilpotent ((LieAlgebra.ad R L) E') :=
    LieAlgebra.isNilpotent_ad_of_isNilpotent hE
  have hintertwine := Module.End.commute_exp_left_of_commute
    hRestricted hAmbient (L.ad_comp_incl_eq E')
  have heq :
      IsNilpotent.exp ((LieAlgebra.ad R
        (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)) E) X =
        ((IsNilpotent.exp ((LieAlgebra.ad R L) E')) X' : L) := by
    simpa [L, E', X', LinearMap.comp_apply] using
      LinearMap.congr_fun hintertwine X'
  rw [← exp_ad_apply hE, heq]
  exact (IsNilpotent.exp ((LieAlgebra.ad R L) E') X').property

private lemma map_eUnipotent_conj_mem_lieAlgebra
    (i : b.support) (t : ℤ)
    {X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R}
    (hX : X ∈ RootPairing.GeckConstruction.lieAlgebra b) :
    (eUnipotent i t).map (algebraMap ℤ R) * X *
        (eUnipotent i (-t)).map (algebraMap ℤ R) ∈
      RootPairing.GeckConstruction.lieAlgebra b := by
  have hnil : IsNilpotent ((t : R) • RootPairing.GeckConstruction.e (P := P) i) :=
    (RootPairing.GeckConstruction.isNilpotent_e i).smul _
  have hmem : (t : R) • RootPairing.GeckConstruction.e (P := P) i ∈
      RootPairing.GeckConstruction.lieAlgebra b :=
    (RootPairing.GeckConstruction.lieAlgebra b).smul_mem _
      (RootPairing.GeckConstruction.e_mem_lieAlgebra i)
  rw [map_eUnipotent_eq_exp, map_eUnipotent_eq_exp]
  convert exp_conj_mem_lieAlgebra (P := P) (b := b) hnil hmem hX using 1 <;>
    simp

private lemma map_fUnipotent_conj_mem_lieAlgebra
    (i : b.support) (t : ℤ)
    {X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R}
    (hX : X ∈ RootPairing.GeckConstruction.lieAlgebra b) :
    (fUnipotent i t).map (algebraMap ℤ R) * X *
        (fUnipotent i (-t)).map (algebraMap ℤ R) ∈
      RootPairing.GeckConstruction.lieAlgebra b := by
  have hnil : IsNilpotent ((t : R) • RootPairing.GeckConstruction.f (P := P) i) :=
    (RootPairing.GeckConstruction.isNilpotent_f i).smul _
  have hmem : (t : R) • RootPairing.GeckConstruction.f (P := P) i ∈
      RootPairing.GeckConstruction.lieAlgebra b :=
    (RootPairing.GeckConstruction.lieAlgebra b).smul_mem _
      (RootPairing.GeckConstruction.f_mem_lieAlgebra i)
  rw [map_fUnipotent_eq_exp, map_fUnipotent_eq_exp]
  convert exp_conj_mem_lieAlgebra (P := P) (b := b) hnil hmem hX using 1 <;>
    simp

private lemma map_titsLift_conj_mem_lieAlgebra
    (i : b.support) {X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R}
    (hX : X ∈ RootPairing.GeckConstruction.lieAlgebra b) :
    (titsLift i).map (algebraMap ℤ R) * X *
        (titsLiftInv i).map (algebraMap ℤ R) ∈
      RootPairing.GeckConstruction.lieAlgebra b := by
  have he := map_eUnipotent_conj_mem_lieAlgebra (P := P) (b := b) i 1 hX
  have hf := map_fUnipotent_conj_mem_lieAlgebra (P := P) (b := b) i (-1) he
  have he' := map_eUnipotent_conj_mem_lieAlgebra (P := P) (b := b) i 1 hf
  simp only [titsLift, titsLiftInv, Matrix.map_mul]
  convert he' using 1 <;> noncomm_ring

private lemma map_titsWord_conj_mem_lieAlgebra
    (word : List b.support) {X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R}
    (hX : X ∈ RootPairing.GeckConstruction.lieAlgebra b) :
    (titsWord word).map (algebraMap ℤ R) * X *
        (titsWordInv word).map (algebraMap ℤ R) ∈
      RootPairing.GeckConstruction.lieAlgebra b := by
  induction word with
  | nil =>
      simpa [titsWord, titsWordInv_nil] using hX
  | cons i word ih =>
      have h := map_titsLift_conj_mem_lieAlgebra (P := P) (b := b) i ih
      simp only [titsWord, titsWordInv_cons, Matrix.map_mul]
      convert h using 1 <;> noncomm_ring

public lemma map_titsConjugate_mem_lieAlgebra
    (word : List b.support) {X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ}
    (hX : X.map (algebraMap ℤ R) ∈ RootPairing.GeckConstruction.lieAlgebra b) :
    (titsConjugate word X).map (algebraMap ℤ R) ∈
      RootPairing.GeckConstruction.lieAlgebra b := by
  rw [titsConjugate_apply, Matrix.map_mul, Matrix.map_mul]
  exact map_titsWord_conj_mem_lieAlgebra (P := P) (b := b) word hX


end
end RootPairing.IntegralGeckConstruction

module

public import Theory.AlgebraicGroup.RootSystems.GeckTitsExponential
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basis

/-!
# Cartan action of mapped Tits lifts

The mapped integral Tits lift acts on Geck's Cartan generators by the corresponding simple
reflection.  The proof calculates the three nilpotent adjoint exponentials and records the
conjugation identities needed to transport root weights.  The argument remains entirely in the
matrix realization supplied by Geck's construction.
-/

namespace RootPairing.IntegralGeckConstruction

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι R M N : Type*} [Field R] [CharZero R] [IsAlgClosed R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private lemma exp_apply_of_sq_apply_eq_zero
    {V : Type*} [AddCommGroup V] [Module R V] [Module ℚ V]
    [IsScalarTower ℚ R V] [SMulCommClass ℚ R V]
    {D : Module.End R V} (hD : IsNilpotent D) {X : V}
    (hzero : (D ^ 2) X = 0) :
    IsNilpotent.exp D X = X + D X := by
  have h := IsNilpotent.exp_smul_eq_sum
    (a := D) (m := X) (k := 2) hzero hD
  simpa [Finset.sum_range_succ] using h

private lemma exp_apply_of_cube_apply_eq_zero
    {V : Type*} [AddCommGroup V] [Module R V] [Module ℚ V]
    [IsScalarTower ℚ R V] [SMulCommClass ℚ R V]
    {D : Module.End R V} (hD : IsNilpotent D) {X : V}
    (hzero : (D ^ 3) X = 0) :
    IsNilpotent.exp D X = X + D X + (2 : ℚ)⁻¹ • (D ^ 2) X := by
  have h := IsNilpotent.exp_smul_eq_sum
    (a := D) (m := X) (k := 3) hzero hD
  simpa [Finset.sum_range_succ] using h

private lemma exp_ad_e_h (i j : b.support) :
    IsNilpotent.exp ((LieAlgebra.ad R
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R))
        (RootPairing.GeckConstruction.e i))
      (RootPairing.GeckConstruction.h j) =
        RootPairing.GeckConstruction.h j -
          (b.cartanMatrix i j : R) • RootPairing.GeckConstruction.e i := by
  let D := (LieAlgebra.ad R
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R))
      (RootPairing.GeckConstruction.e i)
  have hD : IsNilpotent D := LieAlgebra.ad_nilpotent_of_nilpotent
    (RootPairing.GeckConstruction.isNilpotent_e i)
  have hDh : D (RootPairing.GeckConstruction.h j) =
      -(b.cartanMatrix i j : R) • RootPairing.GeckConstruction.e i := by
    change ⁅RootPairing.GeckConstruction.e i,
      RootPairing.GeckConstruction.h j⁆ = _
    rw [← lie_skew, RootPairing.GeckConstruction.lie_h_e]
    simp only [← Int.cast_smul_eq_zsmul R]
    module
  have hDe : D (RootPairing.GeckConstruction.e i) = 0 := by
    change ⁅RootPairing.GeckConstruction.e i,
      RootPairing.GeckConstruction.e i⁆ = 0
    simp [smul_eq_mul]
  have hzero : (D ^ 2) (RootPairing.GeckConstruction.h j) = 0 := by
    rw [pow_two, Module.End.mul_apply, hDh, map_smul, hDe, smul_zero]
  rw [exp_apply_of_sq_apply_eq_zero hD hzero, hDh]
  module

private lemma exp_ad_neg_f_h (i j : b.support) :
    IsNilpotent.exp ((LieAlgebra.ad R
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R))
        (-RootPairing.GeckConstruction.f i))
      (RootPairing.GeckConstruction.h j) =
        RootPairing.GeckConstruction.h j -
          (b.cartanMatrix i j : R) • RootPairing.GeckConstruction.f i := by
  let D := (LieAlgebra.ad R
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R))
      (-RootPairing.GeckConstruction.f i)
  have hD : IsNilpotent D := LieAlgebra.ad_nilpotent_of_nilpotent
    (RootPairing.GeckConstruction.isNilpotent_f i).neg
  have hDh : D (RootPairing.GeckConstruction.h j) =
      -(b.cartanMatrix i j : R) • RootPairing.GeckConstruction.f i := by
    change ⁅-RootPairing.GeckConstruction.f i,
      RootPairing.GeckConstruction.h j⁆ = _
    rw [neg_lie, ← lie_skew, RootPairing.GeckConstruction.lie_h_f]
    simp only [← Int.cast_smul_eq_zsmul R]
    module
  have hDf : D (RootPairing.GeckConstruction.f i) = 0 := by
    change ⁅-RootPairing.GeckConstruction.f i,
      RootPairing.GeckConstruction.f i⁆ = 0
    simp
  have hzero : (D ^ 2) (RootPairing.GeckConstruction.h j) = 0 := by
    rw [pow_two, Module.End.mul_apply, hDh, map_smul, hDf, smul_zero]
  rw [exp_apply_of_sq_apply_eq_zero hD hzero, hDh]
  module

private lemma exp_ad_neg_f_e (i : b.support) :
    IsNilpotent.exp ((LieAlgebra.ad R
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R))
        (-RootPairing.GeckConstruction.f i))
      (RootPairing.GeckConstruction.e i) =
        RootPairing.GeckConstruction.e i + RootPairing.GeckConstruction.h i -
          RootPairing.GeckConstruction.f i := by
  let D := (LieAlgebra.ad R
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R))
      (-RootPairing.GeckConstruction.f i)
  have hD : IsNilpotent D := LieAlgebra.ad_nilpotent_of_nilpotent
    (RootPairing.GeckConstruction.isNilpotent_f i).neg
  have hDe : D (RootPairing.GeckConstruction.e i) =
      RootPairing.GeckConstruction.h i := by
    change ⁅-RootPairing.GeckConstruction.f i,
      RootPairing.GeckConstruction.e i⁆ = _
    rw [neg_lie, lie_skew, RootPairing.GeckConstruction.lie_e_f_same]
  have hDh : D (RootPairing.GeckConstruction.h i) =
      (-(2 : R)) • RootPairing.GeckConstruction.f i := by
    change ⁅-RootPairing.GeckConstruction.f i,
      RootPairing.GeckConstruction.h i⁆ = _
    rw [neg_lie, ← lie_skew, RootPairing.GeckConstruction.lie_h_f]
    simp only [← Int.cast_smul_eq_zsmul R]
    rw [show b.cartanMatrix i i = 2 by simp]
    module
  have hDf : D (RootPairing.GeckConstruction.f i) = 0 := by
    change ⁅-RootPairing.GeckConstruction.f i,
      RootPairing.GeckConstruction.f i⁆ = 0
    simp
  have hzero : (D ^ 3) (RootPairing.GeckConstruction.e i) = 0 := by
    rw [pow_succ, Module.End.mul_apply, pow_two, Module.End.mul_apply,
      hDe, hDh, map_smul, hDf, smul_zero]
  rw [exp_apply_of_cube_apply_eq_zero hD hzero, hDe]
  rw [show (D ^ 2) (RootPairing.GeckConstruction.e i) =
    (-(2 : R)) • RootPairing.GeckConstruction.f i by
      rw [pow_two, Module.End.mul_apply, hDe, hDh]]
  simp only [← Rat.cast_smul_eq_qsmul R]
  module

private lemma exp_ad_e_f (i : b.support) :
    IsNilpotent.exp ((LieAlgebra.ad R
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R))
        (RootPairing.GeckConstruction.e i))
      (RootPairing.GeckConstruction.f i) =
        RootPairing.GeckConstruction.f i + RootPairing.GeckConstruction.h i -
          RootPairing.GeckConstruction.e i := by
  let D := (LieAlgebra.ad R
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R))
      (RootPairing.GeckConstruction.e i)
  have hD : IsNilpotent D := LieAlgebra.ad_nilpotent_of_nilpotent
    (RootPairing.GeckConstruction.isNilpotent_e i)
  have hDf : D (RootPairing.GeckConstruction.f i) =
      RootPairing.GeckConstruction.h i := by
    change ⁅RootPairing.GeckConstruction.e i,
      RootPairing.GeckConstruction.f i⁆ = _
    rw [RootPairing.GeckConstruction.lie_e_f_same]
  have hDh : D (RootPairing.GeckConstruction.h i) =
      (-(2 : R)) • RootPairing.GeckConstruction.e i := by
    change ⁅RootPairing.GeckConstruction.e i,
      RootPairing.GeckConstruction.h i⁆ = _
    rw [← lie_skew, RootPairing.GeckConstruction.lie_h_e]
    simp only [← Int.cast_smul_eq_zsmul R]
    rw [show b.cartanMatrix i i = 2 by simp]
    module
  have hDe : D (RootPairing.GeckConstruction.e i) = 0 := by
    change ⁅RootPairing.GeckConstruction.e i,
      RootPairing.GeckConstruction.e i⁆ = 0
    simp
  have hzero : (D ^ 3) (RootPairing.GeckConstruction.f i) = 0 := by
    rw [pow_succ, Module.End.mul_apply, pow_two, Module.End.mul_apply,
      hDf, hDh, map_smul, hDe, smul_zero]
  rw [exp_apply_of_cube_apply_eq_zero hD hzero, hDf]
  rw [show (D ^ 2) (RootPairing.GeckConstruction.f i) =
    (-(2 : R)) • RootPairing.GeckConstruction.e i by
      rw [pow_two, Module.End.mul_apply, hDf, hDh]]
  simp only [← Rat.cast_smul_eq_qsmul R]
  module

private lemma exp_ad_e_e (i : b.support) :
    IsNilpotent.exp ((LieAlgebra.ad R
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R))
        (RootPairing.GeckConstruction.e i))
      (RootPairing.GeckConstruction.e i) = RootPairing.GeckConstruction.e i := by
  let D := (LieAlgebra.ad R
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R))
      (RootPairing.GeckConstruction.e i)
  have hD : IsNilpotent D := LieAlgebra.ad_nilpotent_of_nilpotent
    (RootPairing.GeckConstruction.isNilpotent_e i)
  have hDe : D (RootPairing.GeckConstruction.e i) = 0 := by
    change ⁅RootPairing.GeckConstruction.e i,
      RootPairing.GeckConstruction.e i⁆ = 0
    simp
  have hzero : (D ^ 2) (RootPairing.GeckConstruction.e i) = 0 := by
    rw [pow_two, Module.End.mul_apply, hDe, map_zero]
  rw [exp_apply_of_sq_apply_eq_zero hD hzero, hDe, add_zero]

private lemma map_titsLift_conj_h (i j : b.support) :
    (titsLift i).map (algebraMap ℤ R) * RootPairing.GeckConstruction.h j *
        (titsLiftInv i).map (algebraMap ℤ R) =
      RootPairing.GeckConstruction.h j -
        (b.cartanMatrix i j : R) • RootPairing.GeckConstruction.h i := by
  let e := RootPairing.GeckConstruction.e (P := P) i
  let f := RootPairing.GeckConstruction.f (P := P) i
  let h : b.support → Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
    fun k => RootPairing.GeckConstruction.h (P := P) k
  have he : IsNilpotent e := RootPairing.GeckConstruction.isNilpotent_e i
  have hf : IsNilpotent f := RootPairing.GeckConstruction.isNilpotent_f i
  simp only [titsLift, titsLiftInv, Matrix.map_mul,
    map_eUnipotent_eq_exp, map_fUnipotent_eq_exp]
  norm_num
  change (IsNilpotent.exp e * IsNilpotent.exp (-f) * IsNilpotent.exp e) * h j *
      (IsNilpotent.exp (-e) * IsNilpotent.exp f * IsNilpotent.exp (-e)) = _
  rw [show (IsNilpotent.exp e * IsNilpotent.exp (-f) * IsNilpotent.exp e) * h j *
      (IsNilpotent.exp (-e) * IsNilpotent.exp f * IsNilpotent.exp (-e)) =
    IsNilpotent.exp e *
      (IsNilpotent.exp (-f) * (IsNilpotent.exp e * h j * IsNilpotent.exp (-e)) *
        IsNilpotent.exp f) * IsNilpotent.exp (-e) by noncomm_ring]
  rw [← exp_ad_apply he]
  rw [show IsNilpotent.exp (-f) *
      (IsNilpotent.exp e * h j * IsNilpotent.exp (-e)) * IsNilpotent.exp f =
        IsNilpotent.exp ((LieAlgebra.ad R
          (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)) (-f))
          (IsNilpotent.exp e * h j * IsNilpotent.exp (-e)) by
    simpa only [neg_neg] using
      (exp_ad_apply (P := P) (b := b) hf.neg
        (IsNilpotent.exp e * h j * IsNilpotent.exp (-e))).symm]
  rw [← exp_ad_apply he]
  rw [exp_ad_e_h]
  rw [map_sub, map_smul, exp_ad_neg_f_h, exp_ad_neg_f_e]
  rw [show (h j - (b.cartanMatrix i j : R) • f) -
      (b.cartanMatrix i j : R) • (e + h i - f) =
        h j - (b.cartanMatrix i j : R) • e -
          (b.cartanMatrix i j : R) • h i by module]
  rw [map_sub, map_sub, map_smul, map_smul,
    exp_ad_e_h, exp_ad_e_e, exp_ad_e_h]
  rw [show b.cartanMatrix i i = 2 by simp]
  module

public lemma map_titsLift_mul_inv (i : b.support) :
    (titsLift i).map (algebraMap ℤ R) *
      (titsLiftInv i).map (algebraMap ℤ R) = 1 := by
  have h := congrArg (fun A => A.map (algebraMap ℤ R))
    (titsLift_mul_inv (P := P) i)
  simpa only [Matrix.map_mul, map_one_matrix] using h

private lemma map_titsLift_inv_mul (i : b.support) :
    (titsLiftInv i).map (algebraMap ℤ R) *
      (titsLift i).map (algebraMap ℤ R) = 1 := by
  have h := congrArg (fun A => A.map (algebraMap ℤ R))
    (titsLift_inv_mul (P := P) i)
  simpa only [Matrix.map_mul, map_one_matrix] using h

public lemma map_titsLift_conj_lie (i : b.support)
    (X Y : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :
    (titsLift i).map (algebraMap ℤ R) * ⁅X, Y⁆ *
        (titsLiftInv i).map (algebraMap ℤ R) =
      ⁅(titsLift i).map (algebraMap ℤ R) * X *
          (titsLiftInv i).map (algebraMap ℤ R),
        (titsLift i).map (algebraMap ℤ R) * Y *
          (titsLiftInv i).map (algebraMap ℤ R)⁆ := by
  let C := (titsLift i).map (algebraMap ℤ R)
  let D := (titsLiftInv i).map (algebraMap ℤ R)
  change C * (X * Y - Y * X) * D =
    (C * X * D) * (C * Y * D) - (C * Y * D) * (C * X * D)
  have h := map_titsLift_inv_mul (P := P) (R := R) (b := b) i
  change D * C = 1 at h
  rw [show (C * X * D) * (C * Y * D) = C * (X * Y) * D by
    calc
      (C * X * D) * (C * Y * D) = C * X * (D * C) * Y * D := by noncomm_ring
      _ = C * (X * Y) * D := by rw [h]; noncomm_ring]
  rw [show (C * Y * D) * (C * X * D) = C * (Y * X) * D by
    calc
      (C * Y * D) * (C * X * D) = C * Y * (D * C) * X * D := by noncomm_ring
      _ = C * (Y * X) * D := by rw [h]; noncomm_ring]
  rw [mul_sub, sub_mul]

public lemma map_titsLiftInv_conj_h (i j : b.support) :
    (titsLiftInv i).map (algebraMap ℤ R) * RootPairing.GeckConstruction.h j *
        (titsLift i).map (algebraMap ℤ R) =
      RootPairing.GeckConstruction.h j -
        (b.cartanMatrix i j : R) • RootPairing.GeckConstruction.h i := by
  let C := (titsLift i).map (algebraMap ℤ R)
  let D := (titsLiftInv i).map (algebraMap ℤ R)
  let h : b.support → Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
    fun k => RootPairing.GeckConstruction.h (P := P) k
  let a : R := b.cartanMatrix i j
  have hCi := map_titsLift_conj_h (P := P) (R := R) (b := b) i i
  have hCj := map_titsLift_conj_h (P := P) (R := R) (b := b) i j
  have hCD := map_titsLift_mul_inv (P := P) (R := R) (b := b) i
  have hDC := map_titsLift_inv_mul (P := P) (R := R) (b := b) i
  have hii : (b.cartanMatrix i i : R) = 2 := by
    norm_num [show b.cartanMatrix i i = 2 by simp]
  have hfix : C * (h j - a • h i) * D = h j := by
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hCj, hCi]
    rw [hii]
    change (h j - a • h i) - a • (h i - (2 : R) • h i) = h j
    module
  change D * h j * C = h j - a • h i
  calc
    D * h j * C = D * (C * (h j - a • h i) * D) * C := by rw [hfix]
    _ = (D * C) * (h j - a • h i) * (D * C) := by noncomm_ring
    _ = h j - a • h i := by rw [hDC, Matrix.one_mul, Matrix.mul_one]


end
end RootPairing.IntegralGeckConstruction

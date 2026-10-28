module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.MatrixRelations.IntegralB2
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.DividedPowers
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Finite exponentials for the B₂ root-block swap

The integral brackets `[S,R] = εC` and `[S,C] = 2δD`, together with the four
zero brackets, imply the root-curve swap. We first calculate conjugation by a
nilpotent exponential in a rational algebra. Its adjoint series terminates
after the second bracket. Factoring the resulting commuting exponentials gives
the ordered correction factors with parameters `εab` and `-εδab²`.

For the actual F₄ representation the cubic divided power vanishes. Its
quadratic root curve therefore agrees with this exponential in characteristic
zero. Apply the calculation over `ℚ[X,Y]`, use coefficientwise injectivity to
descend to `ℤ[X,Y]`, and evaluate in the Ree coefficient field. Both integral
signs then become one. In particular, this argument also applies at `m = 0`.

The adjoint-exponential argument generalizes the matrix calculation in
`GeckTitsExponential`; finite exponentials and their functoriality are from
Mathlib's `RingTheory.Nilpotent.Exp`. Source: the B₂ Chevalley calculation
underlying Aschbacher–Smith F.1.12(I)(5), `refs/quasithin.pdf`, printed p.263
(PDF p.274). This theorem is conditional on the stated integral brackets;
their construction is a separate obligation.
-/

public section

namespace ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates.MatrixRelations

open scoped Classical Matrix
open IsNilpotent
noncomputable section
section Abstract
variable {A : Type*} [Ring A] [Algebra ℚ A]
attribute [local instance 100] LieRing.ofAssociativeRing

private lemma exp_mulLeft {E : A} (hE : IsNilpotent E) (X : A) :
    exp (LinearMap.mulLeft ℚ E) X = exp E * X := by
  obtain ⟨n, hn⟩ := hE
  have hp (k : ℕ) (Y : A) : (LinearMap.mulLeft ℚ E ^ k) Y = E ^ k * Y := by
    simp
  have hL : (LinearMap.mulLeft ℚ E) ^ n = 0 := by
    ext Y
    simp only [hp, hn, zero_mul, LinearMap.zero_apply]
  rw [exp_eq_sum hL, exp_eq_sum hn]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, hp,
    Finset.sum_mul, smul_mul_assoc]

private lemma exp_mulRight {E : A} (hE : IsNilpotent E) (X : A) :
    exp (LinearMap.mulRight ℚ E) X = X * exp E := by
  obtain ⟨n, hn⟩ := hE
  have hp (k : ℕ) (Y : A) : (LinearMap.mulRight ℚ E ^ k) Y = Y * E ^ k := by
    simp
  have hL : (LinearMap.mulRight ℚ E) ^ n = 0 := by
    ext Y
    simp only [hp, hn, mul_zero, LinearMap.zero_apply]
  rw [exp_eq_sum hL, exp_eq_sum hn]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, hp,
    Finset.mul_sum, mul_smul_comm]

private lemma exp_ad {E : A} (hE : IsNilpotent E) (X : A) :
    exp ((LieAlgebra.ad ℚ A) E) X = exp E * X * exp (-E) := by
  let L := LinearMap.mulLeft ℚ E
  let Q := LinearMap.mulRight ℚ E
  have hL : IsNilpotent L := (LinearMap.isNilpotent_mulLeft_iff ℚ E).2 hE
  have hQ : IsNilpotent Q := (LinearMap.isNilpotent_mulRight_iff ℚ E).2 hE
  have hcomm : Commute L (-Q) := by
    ext Y
    simp [L, Q, Module.End.mul_apply, mul_assoc]
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  change exp (L - Q) X = _
  rw [sub_eq_add_neg, exp_add_of_commute hcomm hL hQ.neg]
  change exp L (exp (-Q) X) = _
  rw [show -Q = LinearMap.mulRight ℚ (-E) by ext Y; simp [Q]]
  rw [exp_mulRight hE.neg, exp_mulLeft hE]
  simp only [mul_assoc]

private lemma exp_conj {E X : A} (hE : IsNilpotent E) (hX : IsNilpotent X) :
    exp E * exp X * exp (-E) = exp (exp E * X * exp (-E)) := by
  let f : A →+* A :=
    { toFun := fun Y => exp E * Y * exp (-E)
      map_one' := by simpa using hE.exp_mul_exp_neg_self
      map_mul' := by
        intro Y Z
        simp only [mul_assoc]
        rw [← mul_assoc (exp (-E)) (exp E), hE.exp_neg_mul_exp_self, one_mul]
      map_zero' := by simp
      map_add' := by intros; simp only [mul_add, add_mul] }
  exact hX.map_exp f

private lemma conj_of_brackets {X Y Z W : A} (hY : IsNilpotent Y)
    (hYX : Y * X - X * Y = Z) (hYZ : Y * Z - Z * Y = (2 : ℚ) • W)
    (hYW : Commute Y W) :
    exp Y * X * exp (-Y) = X + Z + W := by
  let D := (LieAlgebra.ad ℚ A) Y
  have hDX : D X = Z := hYX
  have hDZ : D Z = (2 : ℚ) • W := hYZ
  have hDW : D W = 0 := sub_eq_zero.mpr hYW.eq
  have hD := LieAlgebra.ad_nilpotent_of_nilpotent (R := ℚ) hY
  have hz : (D ^ 3) X = 0 := by
    change D (D (D X)) = 0
    rw [hDX, hDZ, map_smul, hDW, smul_zero]
  have he := exp_smul_eq_sum (a := D) (m := X) hz hD
  change exp D X = _ at he
  rw [← exp_ad hY]
  simpa [Finset.sum_range_succ, pow_two, Module.End.mul_apply, hDX, hDZ,
    smul_smul] using he

private lemma exp_swap {X Y Z W : A}
    (hX : IsNilpotent X) (hY : IsNilpotent Y)
    (hZ : IsNilpotent Z) (hW : IsNilpotent W)
    (hYX : Y * X - X * Y = Z) (hYZ : Y * Z - Z * Y = (2 : ℚ) • W)
    (hXZ : Commute X Z) (hXW : Commute X W)
    (hYW : Commute Y W) (hZW : Commute Z W) :
    exp Y * exp X = exp X * exp Y * exp Z * exp (-W) := by
  have hc : exp (-Y) * X * exp Y = X + -Z + W := by
    simpa only [neg_neg] using conj_of_brackets hY.neg
      (X := X) (Z := -Z) (W := W)
      (by calc
        _ = -(Y * X - X * Y) := by noncomm_ring
        _ = -Z := by rw [hYX])
      (by simpa only [neg_mul, mul_neg, neg_neg] using hYZ) hYW.neg_left
  have he : exp (-Y) * exp X * exp Y = exp X * exp (-Z) * exp W := by
    have hh := exp_conj hY.neg hX
    simp only [neg_neg] at hh
    rw [hh, hc,
      exp_add_of_commute (hXW.add_left hZW.neg_left)
        (hXZ.neg_right.isNilpotent_add hX hZ.neg) hW,
      exp_add_of_commute hXZ.neg_right hX hZ.neg]
  have hcancel : exp (-Z) * exp W * (exp Z * exp (-W)) = 1 := by
    have hwz : exp W * exp Z = exp Z * exp W := by
      rw [← exp_add_of_commute hZW.symm hW hZ,
        ← exp_add_of_commute hZW hZ hW, add_comm W Z]
    calc
      _ = exp (-Z) * (exp W * exp Z) * exp (-W) := by simp only [mul_assoc]
      _ = exp (-Z) * (exp Z * exp W) * exp (-W) := by rw [hwz]
      _ = 1 := by rw [← mul_assoc, hZ.exp_neg_mul_exp_self, one_mul,
        hW.exp_mul_exp_neg_self]
  calc
    exp Y * exp X = exp Y * (exp X * exp (-Z) * exp W) * (exp Z * exp (-W)) := by
      simpa only [mul_assoc, mul_one] using
        congrArg (fun T => exp Y * (exp X * T)) hcancel.symm
    _ = exp Y * (exp (-Y) * exp X * exp Y) * (exp Z * exp (-W)) := by rw [he]
    _ = exp X * exp Y * exp Z * exp (-W) := by
      simp only [← mul_assoc]
      rw [hY.exp_mul_exp_neg_self, one_mul]

end Abstract

open Theory.AlgebraicGroup
open RootPairing.IntegralGeckConstruction

private abbrev op {K : Type*} [CommRing K] (r : F4Chevalley.Root) :
    Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex K :=
  specializeMatrix (F4Chevalley.integralOperators.rootOperator r)

private lemma op_nilpotent {K : Type*} [CommRing K] (r : F4Chevalley.Root) :
    IsNilpotent (op (K := K) r) :=
  by
    obtain ⟨n, hn⟩ := F4Chevalley.operator_isNilpotent r
    refine ⟨n, ?_⟩
    change (F4Chevalley.integralOperators.rootOperator r).map (Int.castRingHom K) ^ n = 0
    rw [← Matrix.map_pow, hn]
    exact Matrix.map_zero _ (map_zero _)

private lemma curve_exp {K : Type*} [CommRing K] [Algebra ℚ K]
    (r : F4Chevalley.Root) (t : K) :
    (F4Chevalley.rootCurve r t : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex K) =
      exp (t • op r) := by
  have hp (n : ℕ) : op (K := K) r ^ n =
      n.factorial • specializeMatrix (S := K)
        (F4Chevalley.integralOperators.rootDividedPower r n) := by
    have hh := congrArg (Int.castRingHom K).mapMatrix
      (F4Chevalley.operator_pow_eq_factorial_smul r n)
    simpa only [op, specializeMatrix, RingHom.mapMatrix_apply, Matrix.map_pow, map_nsmul] using hh
  have hc : (t • op (K := K) r) ^ 3 = 0 := by
    rw [smul_pow, hp, ReeF4.WordRelations.rootDividedPower_three,
      specializeMatrix_zero, smul_zero, smul_zero]
  have htwo : (2 : ℚ)⁻¹ • op (K := K) r ^ 2 =
      specializeMatrix (S := K) (F4Chevalley.integralOperators.rootDividedPower r 2) := by
    rw [hp]
    norm_num [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  rw [ReeF4.WordRelations.rootCurve_quadratic, F4Chevalley.dividedPower_one,
    exp_eq_sum hc]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
    Nat.factorial_one, pow_one, Nat.factorial_two, Nat.cast_ofNat]
  rw [smul_pow, smul_comm (2 : ℚ)⁻¹, htwo]

private lemma curve_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (r : F4Chevalley.Root) (t : K) :
    f.mapMatrix (F4Chevalley.rootCurve r t : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex K) =
      (F4Chevalley.rootCurve r (f t) : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex L) := by
  rw [RingHom.mapMatrix_apply, F4Chevalley.rootCurve_matrix_formula,
    F4Chevalley.rootCurve_matrix_formula]
  ext i j
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    specializeMatrix, Matrix.one_apply, apply_ite f]

private lemma curve_swap_rational {K : Type*} [CommRing K] [Algebra ℚ K]
    (r s c d : F4Chevalley.Root) (h : IntegralB2Relations r s c d)
    (ε δ : ℤ)
    (hε : F4Chevalley.integralOperators.rootOperator s *
        F4Chevalley.integralOperators.rootOperator r -
      F4Chevalley.integralOperators.rootOperator r *
        F4Chevalley.integralOperators.rootOperator s =
      ε • F4Chevalley.integralOperators.rootOperator c)
    (hδ : F4Chevalley.integralOperators.rootOperator s *
        F4Chevalley.integralOperators.rootOperator c -
      F4Chevalley.integralOperators.rootOperator c *
        F4Chevalley.integralOperators.rootOperator s =
      (2 * δ) • F4Chevalley.integralOperators.rootOperator d)
    (a b : K) :
    (F4Chevalley.rootCurve s b : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex K) *
      F4Chevalley.rootCurve r a =
    F4Chevalley.rootCurve r a * F4Chevalley.rootCurve s b *
      F4Chevalley.rootCurve c ((ε : K) * a * b) *
      F4Chevalley.rootCurve d (-((ε : K) * δ * a * b ^ 2)) := by
  let f := (Int.castRingHom K).mapMatrix (m := F4Chevalley.BasisIndex)
  have hb1 : op (K := K) s * op r - op r * op s = (ε : K) • op c := by
    simpa only [map_sub, map_mul, map_zsmul, Int.cast_smul_eq_zsmul,
      f, RingHom.mapMatrix_apply, op, specializeMatrix] using congrArg f hε
  have hb2 : op (K := K) s * op c - op c * op s = (2 * (δ : K)) • op d := by
    have hh := congrArg f hδ
    simpa only [map_sub, map_mul, map_zsmul, ← Int.cast_smul_eq_zsmul K,
      Int.cast_mul, Int.cast_ofNat, f, RingHom.mapMatrix_apply, op, specializeMatrix] using hh
  have hc' (u v : F4Chevalley.Root)
      (huv : Commute (F4Chevalley.integralOperators.rootOperator u)
        (F4Chevalley.integralOperators.rootOperator v)) :
      Commute (op (K := K) u) (op v) := huv.map f
  have hYX : (b • op (K := K) s) * (a • op r) - (a • op r) * (b • op s) =
      ((ε : K) * a * b) • op c := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm b a, ← smul_sub, hb1, smul_smul]
    congr 1
    ring
  have hYZ : (b • op (K := K) s) * (((ε : K) * a * b) • op c) -
      (((ε : K) * a * b) • op c) * (b • op s) =
      (2 : ℚ) • (((ε : K) * δ * a * b ^ 2) • op d) := by
    rw [show (2 : ℚ) • (((ε : K) * δ * a * b ^ 2) • op d) =
      (2 : K) • (((ε : K) * δ * a * b ^ 2) • op d) by simp only [two_smul]]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm b, ← smul_sub, hb2, smul_smul]
    congr 1
    ring
  simp only [curve_exp]
  rw [neg_smul]
  exact exp_swap ((op_nilpotent r).smul a) ((op_nilpotent s).smul b)
    ((op_nilpotent c).smul _) ((op_nilpotent d).smul _) hYX hYZ
    (((hc' r c h.long_sum).smul_left _).smul_right _)
    (((hc' r d h.long_top).smul_left _).smul_right _)
    (((hc' s d h.short_top).smul_left _).smul_right _)
    (((hc' c d h.sum_top).smul_left _).smul_right _)

private lemma curve_swap_integral {K : Type*} [CommRing K]
    (r s c d : F4Chevalley.Root) (h : IntegralB2Relations r s c d)
    (ε δ : ℤ)
    (hε : F4Chevalley.integralOperators.rootOperator s *
        F4Chevalley.integralOperators.rootOperator r -
      F4Chevalley.integralOperators.rootOperator r *
        F4Chevalley.integralOperators.rootOperator s =
      ε • F4Chevalley.integralOperators.rootOperator c)
    (hδ : F4Chevalley.integralOperators.rootOperator s *
        F4Chevalley.integralOperators.rootOperator c -
      F4Chevalley.integralOperators.rootOperator c *
        F4Chevalley.integralOperators.rootOperator s =
      (2 * δ) • F4Chevalley.integralOperators.rootOperator d)
    (a b : K) :
    (F4Chevalley.rootCurve s b : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex K) *
      F4Chevalley.rootCurve r a =
    F4Chevalley.rootCurve r a * F4Chevalley.rootCurve s b *
      F4Chevalley.rootCurve c ((ε : K) * a * b) *
      F4Chevalley.rootCurve d (-((ε : K) * δ * a * b ^ 2)) := by
  let P := MvPolynomial Bool ℤ
  let x : P := MvPolynomial.X false
  let y : P := MvPolynomial.X true
  have hi : (F4Chevalley.rootCurve s y : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex P) *
        F4Chevalley.rootCurve r x =
      F4Chevalley.rootCurve r x * F4Chevalley.rootCurve s y *
        F4Chevalley.rootCurve c ((ε : P) * x * y) *
        F4Chevalley.rootCurve d (-((ε : P) * δ * x * y ^ 2)) := by
    let f : P →+* MvPolynomial Bool ℚ := MvPolynomial.map (Int.castRingHom ℚ)
    apply Matrix.map_injective (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)
    change f.mapMatrix _ = f.mapMatrix _
    simp only [map_mul, curve_map, map_neg, map_pow, map_intCast]
    exact curve_swap_rational r s c d h ε δ hε hδ (f x) (f y)
  let f : P →+* K := MvPolynomial.eval₂Hom (Int.castRingHom K)
    (fun i => if i then b else a)
  have he := congrArg f.mapMatrix hi
  have fx : f x = a := by simp [f, x, P]
  have fy : f y = b := by simp [f, y, P]
  simpa only [map_mul, curve_map, map_neg, map_pow, map_intCast, fx, fy] using he

/-- The B₂ root-curve swap from integral bracket data, for every Ree parameter.
The signed identity is descended from rational to integral polynomials before
specialization; no factorial is cancelled in the characteristic-two field. -/
theorem rootCurve_swap_of_integralB2 (m : ℕ) (r s c d : F4Chevalley.Root)
    (h : IntegralB2Relations r s c d) (a b : CoefficientField m) :
    F4Chevalley.rootCurve s b * F4Chevalley.rootCurve r a =
      F4Chevalley.rootCurve r a * F4Chevalley.rootCurve s b *
        F4Chevalley.rootCurve c (a * b) * F4Chevalley.rootCurve d (a * b ^ 2) := by
  obtain ⟨ε, hε2, hε⟩ := h.short_long
  obtain ⟨δ, hδ2, hδ⟩ := h.short_sum
  have hsign (z : ℤ) (hz : z ^ 2 = 1) : (z : CoefficientField m) = 1 := by
    have hh : z = 1 ∨ z = -1 := (sq_eq_one_iff).mp hz
    rcases hh with rfl | rfl <;> simp [CharTwo.neg_eq]
  apply Units.ext
  simpa only [Units.val_mul, hsign ε hε2, hsign δ hδ2, one_mul,
    CharTwo.neg_eq] using curve_swap_integral r s c d h ε δ hε hδ a b

end
end ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates.MatrixRelations

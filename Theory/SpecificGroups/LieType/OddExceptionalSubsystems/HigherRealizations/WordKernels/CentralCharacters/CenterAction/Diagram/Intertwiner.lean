module

public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup

/-!
# Integral operator intertwiners and the full simple-root curves

An intertwiner of signed simple operators intertwines every divided power,
with the corresponding power of the parameter multiplier. Cancel factorials
entrywise over the integers, then change coefficients and evaluate the cubic
root curves. In particular no division by two or three is made in the target
ring. Invertible intertwiners give identities of actual matrix units.

Source: the integral Geck construction, GLS3 §1.12 and Remark 1.12.10.
The higher E6 applications are in the parent `Diagram` module.
-/

@[expose] public section
noncomputable section
namespace RootPairing.IntegralGeckConstruction
open Matrix RootPairing.SimpleGeckGroup
variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

lemma signed_pow_factorial (x : Bool × b.support) (n : ℕ) :
    (simpleFamily (b := b)).dividedPower x 1 ^ n =
      n.factorial • (simpleFamily (b := b)).dividedPower x n := by
  rcases x with ⟨s, i⟩
  cases s
  · simpa only [simpleFamily, fDividedPower_one] using fMatrix_pow_eq_factorial_smul i n
  · simpa only [simpleFamily, eDividedPower_one] using eMatrix_pow_eq_factorial_smul i n

lemma signed_dividedPower_intertwine
    (C : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
    (x y : Bool × b.support) (a : ℤ)
    (h : C * (simpleFamily (b := b)).dividedPower x 1 =
      (a • (simpleFamily (b := b)).dividedPower y 1) * C) (n : ℕ) :
    C * (simpleFamily (b := b)).dividedPower x n =
      (a ^ n • (simpleFamily (b := b)).dividedPower y n) * C := by
  have hn := (show SemiconjBy C _ _ from h).pow_right n
  rw [smul_pow, signed_pow_factorial, signed_pow_factorial] at hn
  have hn' : n.factorial • (C * (simpleFamily (b := b)).dividedPower x n) =
      n.factorial • ((a ^ n • (simpleFamily (b := b)).dividedPower y n) * C) := by
    simpa only [SemiconjBy, mul_smul_comm, smul_mul_assoc, smul_comm (a ^ n)] using hn
  ext k l
  exact nsmul_right_injective (Nat.factorial_ne_zero n)
    (congrFun (congrFun hn' k) l)

lemma signed_curve_intertwine {S : Type*} [CommRing S]
    (C : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
    (x y : Bool × b.support) (a : ℤ)
    (h : C * (simpleFamily (b := b)).dividedPower x 1 =
      (a • (simpleFamily (b := b)).dividedPower y 1) * C) (t : S) :
    C.map (Int.castRingHom S) * (simpleFamily (b := b)).curve x t =
      (simpleFamily (b := b)).curve y ((a : S) * t) * C.map (Int.castRingHom S) := by
  have hn (n : ℕ) :
      C.map (Int.castRingHom S) * (simpleFamily (b := b)).coefficient x n =
        ((a : S) ^ n • (simpleFamily (b := b)).coefficient y n) *
          C.map (Int.castRingHom S) := by
    have hh := congrArg (Int.castRingHom S).mapMatrix
      (signed_dividedPower_intertwine C x y a h n)
    simp only [map_mul, map_zsmul] at hh
    simpa only [← Int.cast_smul_eq_zsmul S, Int.cast_pow, RingHom.mapMatrix_apply,
      IntegralCubicFamily.coefficient] using hh
  simp only [IntegralCubicFamily.curve, mul_add, add_mul, mul_one, one_mul,
    mul_smul_comm, hn, smul_mul_assoc, smul_smul, mul_pow]
  module

lemma signed_unit_intertwine {S : Type*} [CommRing S]
    (C : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)ˣ)
    (x y : Bool × b.support) (a : ℤ)
    (h : C.val * (simpleFamily (b := b)).dividedPower x 1 =
      (a • (simpleFamily (b := b)).dividedPower y 1) * C.val) (t : S) :
    Units.map (Int.castRingHom S).mapMatrix.toMonoidHom C *
        (simpleFamily (b := b)).unit x t =
      (simpleFamily (b := b)).unit y ((a : S) * t) *
        Units.map (Int.castRingHom S).mapMatrix.toMonoidHom C := by
  apply Units.ext
  exact signed_curve_intertwine C.val x y a h t
end RootPairing.IntegralGeckConstruction

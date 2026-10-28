module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.EqualLength.QuadraticAlgebra
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.DividedPowers
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Central root-curve exchanges over arbitrary coefficient rings

Apply the torsion-free quadratic exponential identity over the integer
polynomial ring in two parameters. Evaluation then gives the actual root
matrix exchange over every commutative ring, including characteristic two.
In particular no factorial is cancelled after coefficient specialization.
The operator bracket and its centrality are explicit hypotheses here.

Source: the Chevalley finite-exponential calculation underlying
Aschbacher–Smith F.1.12(I)(5), printed p.263 of `refs/quasithin.pdf`.
-/

public section
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Matrix
namespace ReeF4.Parabolics.RadicalCoordinates.EqualLength
noncomputable section

private lemma scaled_square {K : Type*} [CommRing K] (r : F4Chevalley.Root) (a : K) :
    (a • specializeMatrix (S := K) (F4Chevalley.integralOperators.rootOperator r)) *
      (a • specializeMatrix (S := K) (F4Chevalley.integralOperators.rootOperator r)) =
        (2 : ℕ) • (a^2 • specializeMatrix (S := K)
          (F4Chevalley.integralOperators.rootDividedPower r 2)) := by
  have h := congrArg (fun A : F4Chevalley.IntegralMatrix => specializeMatrix (S := K) A)
    (F4Chevalley.operator_pow_eq_factorial_smul r 2)
  simp only [specializeMatrix, Matrix.map_pow, Matrix.map_smul _ _ (map_nsmul _ _)] at h
  norm_num only [Nat.factorial] at h
  change specializeMatrix (S := K) (F4Chevalley.integralOperators.rootOperator r)^2 =
    (2 : ℕ) • specializeMatrix (S := K) (F4Chevalley.integralOperators.rootDividedPower r 2) at h
  rw [smul_mul_smul_comm, ← pow_two a, ← pow_two, h, smul_comm]

private lemma scaled_cube {K : Type*} [CommRing K] (r : F4Chevalley.Root) (a : K) :
    (a • specializeMatrix (S := K) (F4Chevalley.integralOperators.rootOperator r))^3 = 0 := by
  have h := congrArg (fun A : F4Chevalley.IntegralMatrix => specializeMatrix (S := K) A)
    (F4Chevalley.operator_pow_eq_factorial_smul r 3)
  rw [WordRelations.rootDividedPower_three, smul_zero, specializeMatrix_zero] at h
  change (F4Chevalley.integralOperators.rootOperator r ^ 3).map (Int.castRingHom K) = 0 at h
  rw [Matrix.map_pow] at h
  change specializeMatrix (S := K) (F4Chevalley.integralOperators.rootOperator r)^3 = 0 at h
  rw [smul_pow, h, smul_zero]

private lemma exchange_torsionFree {K : Type*} [CommRing K] [IsAddTorsionFree K]
    (r s t : F4Chevalley.Root) (n : ℤ)
    (hn : F4Chevalley.integralOperators.rootOperator r *
        F4Chevalley.integralOperators.rootOperator s -
      F4Chevalley.integralOperators.rootOperator s * F4Chevalley.integralOperators.rootOperator r =
        n • F4Chevalley.integralOperators.rootOperator t)
    (hrt : Commute (F4Chevalley.integralOperators.rootOperator r)
      (F4Chevalley.integralOperators.rootOperator t))
    (hst : Commute (F4Chevalley.integralOperators.rootOperator s)
      (F4Chevalley.integralOperators.rootOperator t)) (a b : K) :
    (F4Chevalley.rootCurve r a).val * (F4Chevalley.rootCurve s b).val =
      (F4Chevalley.rootCurve s b).val * (F4Chevalley.rootCurve r a).val *
        (F4Chevalley.rootCurve t ((n : K)*a*b)).val := by
  let : IsAddTorsionFree (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex K) :=
    inferInstanceAs (IsAddTorsionFree (F4Chevalley.BasisIndex → F4Chevalley.BasisIndex → K))
  let A := specializeMatrix (S := K) (F4Chevalley.integralOperators.rootOperator r)
  let B := specializeMatrix (S := K) (F4Chevalley.integralOperators.rootOperator s)
  let D := specializeMatrix (S := K) (F4Chevalley.integralOperators.rootOperator t)
  have hab : (a • A)*(b • B)-(b • B)*(a • A) = ((n : K)*a*b) • D := by
    have h := congrArg (fun A : F4Chevalley.IntegralMatrix =>
      A.map (Int.castRingHom K)) hn
    simp only [Matrix.map_sub _ (map_sub _), Matrix.map_mul,
      Matrix.map_smul _ _ (map_zsmul _ _), ← Int.cast_smul_eq_zsmul K] at h
    change A*B-B*A = (n : K) • D at h
    calc
      _ = (a*b) • (A*B-B*A) := by
        simp only [smul_mul_smul_comm, smul_sub]
        rw [mul_comm b a]
      _ = _ := by rw [h]; module
  have hAD : Commute (a • A) (((n : K)*a*b) • D) :=
    ((hrt.map (Int.castRingHom K).mapMatrix).smul_left a).smul_right _
  have hBD : Commute (b • B) (((n : K)*a*b) • D) :=
    ((hst.map (Int.castRingHom K).mapMatrix).smul_left b).smul_right _
  rw [WordRelations.rootCurve_quadratic, WordRelations.rootCurve_quadratic,
    WordRelations.rootCurve_quadratic]
  simp only [F4Chevalley.dividedPower_one]
  exact quadratic_exchange_of_central_bracket _ _ _ _ _ _ hab hAD hBD
    (scaled_square r a) (scaled_square s b) (scaled_square t _)
    (scaled_cube r a) (scaled_cube s b)

private lemma map_rootCurve {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (r : F4Chevalley.Root) (a : K) :
    (F4Chevalley.rootCurve r a).val.map f = (F4Chevalley.rootCurve r (f a)).val := by
  classical
  rw [WordRelations.rootCurve_quadratic, WordRelations.rootCurve_quadratic]
  ext i j
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    specializeMatrix, Matrix.one_apply, apply_ite f]

/-- A central integral operator bracket gives the full root-curve exchange over
any commutative ring. The proof includes the quadratic divided powers. -/
theorem rootCurve_exchange_of_central_integral_bracket {K : Type*} [CommRing K]
    (r s t : F4Chevalley.Root) (n : ℤ)
    (hn : F4Chevalley.integralOperators.rootOperator r *
        F4Chevalley.integralOperators.rootOperator s -
      F4Chevalley.integralOperators.rootOperator s * F4Chevalley.integralOperators.rootOperator r =
        n • F4Chevalley.integralOperators.rootOperator t)
    (hrt : Commute (F4Chevalley.integralOperators.rootOperator r)
      (F4Chevalley.integralOperators.rootOperator t))
    (hst : Commute (F4Chevalley.integralOperators.rootOperator s)
      (F4Chevalley.integralOperators.rootOperator t)) (a b : K) :
    (F4Chevalley.rootCurve r a).val * (F4Chevalley.rootCurve s b).val =
      (F4Chevalley.rootCurve s b).val * (F4Chevalley.rootCurve r a).val *
        (F4Chevalley.rootCurve t ((n : K)*a*b)).val := by
  let S := MvPolynomial (Fin 2) ℤ
  let x : S := MvPolynomial.X 0
  let y : S := MvPolynomial.X 1
  let f : S →+* K := MvPolynomial.eval₂Hom (Int.castRingHom K) ![a,b]
  have h := congrArg (fun A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex S => A.map f)
    (exchange_torsionFree r s t n hn hrt hst x y)
  have hx : f x = a := by
    change (MvPolynomial.eval₂Hom (Int.castRingHom K) ![a,b]) (MvPolynomial.X (0 : Fin 2)) = a
    rw [MvPolynomial.eval₂Hom_X']
    rfl
  have hy : f y = b := by
    change (MvPolynomial.eval₂Hom (Int.castRingHom K) ![a,b]) (MvPolynomial.X (1 : Fin 2)) = b
    rw [MvPolynomial.eval₂Hom_X']
    rfl
  simpa only [Matrix.map_mul, map_rootCurve, map_mul, map_intCast, hx, hy] using h

end
end ReeF4.Parabolics.RadicalCoordinates.EqualLength

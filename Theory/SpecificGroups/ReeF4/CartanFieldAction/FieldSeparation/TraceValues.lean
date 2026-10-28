module

public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.RootWitness
public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues.DividedPowers
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.CharP.Two
/-!
# Traces of the actual fixed Ree end-root words

The certified integral end-root matrices give the trace polynomial
`52 + 18*t + 36*u + t² + 7*u² + 10*t*u + 2*t*u²`. Scalar extension and
characteristic two reduce it to `t² + u²`. Substituting `u = t^(2^m)` in the
existing fixed-group witness gives `t² + t^(2^(m+1))` without any simplicity,
automorphism-coverage, or separation assumption.

This is the concrete trace input for the field/inner-diagonal separation
argument. It includes the full fixed group at `m = 0`, independently of the
Tits simple carrier. Source: GLS3 Table 2.4, type VI, and Theorem 2.5.12(a)
(`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith A.3.15(5), printed pp.50–51,
and the proof of Proposition 1.3.4, printed p.511 (`refs/quasithin.pdf`).
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace ReeF4.Cartan.FieldSeparation.TraceValues
noncomputable section
open scoped Matrix
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
variable {S : Type*} [CommRing S]

lemma reindex_map (A : F4Chevalley.IntegralMatrix) :
    reindex (A.map (Int.castRingHom S)) = (reindex A).map (Int.castRingHom S) := rfl

lemma reindex_smul (t : S) (A : Matrix Basis Basis S) :
    reindex (t • A) = t • reindex A := rfl

lemma trace_reindex (A : Matrix Basis Basis S) :
    Matrix.trace (reindex A) = Matrix.trace A := by
  change (∑ i : Fin 52, A (basisEquiv i) (basisEquiv i)) = ∑ j : Basis, A j j
  exact Equiv.sum_comp basisEquiv (fun j => A j j)

lemma positiveMatrix_0 (t : S) :
    reindex (positiveMatrix (typeF4RootPairing_baseEquiv 0) t) = positive0 t := by
  rw [positiveMatrix_formula]
  simp only [map_add, map_one, reindex_smul, reindex_map, eDividedPower_one,
    eMatrix_0, eDividedPower_0_two, eDividedPower_0_three]
  simp only [positive0, Fin.sum_univ_three]
  change (1 + t • (matrix positive0Linear).map (Int.castRingHom S) +
    t ^ 2 • (matrix positive0Quadratic).map (Int.castRingHom S) +
    t ^ 3 • (0 : Matrix (Fin 52) (Fin 52) ℤ).map (Int.castRingHom S)) =
    t ^ 0 • scalarMatrix identityEntries + t ^ 1 • scalarMatrix positive0Linear +
      t ^ 2 • scalarMatrix positive0Quadratic
  simp [scalarMatrix, matrix_identity]

lemma positiveMatrix_3 (t : S) :
    reindex (positiveMatrix (typeF4RootPairing_baseEquiv 3) t) = positive3 t := by
  rw [positiveMatrix_formula]
  simp only [map_add, map_one, reindex_smul, reindex_map, eDividedPower_one,
    eMatrix_3, eDividedPower_3_two, eDividedPower_3_three]
  simp only [positive3, Fin.sum_univ_three]
  change (1 + t • (matrix positive3Linear).map (Int.castRingHom S) +
    t ^ 2 • (matrix positive3Quadratic).map (Int.castRingHom S) +
    t ^ 3 • (0 : Matrix (Fin 52) (Fin 52) ℤ).map (Int.castRingHom S)) =
    t ^ 0 • scalarMatrix identityEntries + t ^ 1 • scalarMatrix positive3Linear +
      t ^ 2 • scalarMatrix positive3Quadratic
  simp [scalarMatrix, matrix_identity]

lemma negativeMatrix_0 :
    reindex (negativeMatrix (typeF4RootPairing_baseEquiv 0) (1 : S)) = negative0 := by
  rw [negativeMatrix_formula]
  simp only [map_add, map_one, reindex_smul, reindex_map, fDividedPower_one,
    fMatrix_0, fDividedPower_0_two, fDividedPower_0_three]
  simp [negative0, negative0Entries, scalarMatrix, matrix_append, matrix_identity, Matrix.map_add, Matrix.map_one, add_assoc]

lemma negativeMatrix_3 :
    reindex (negativeMatrix (typeF4RootPairing_baseEquiv 3) (1 : S)) = negative3 := by
  rw [negativeMatrix_formula]
  simp only [map_add, map_one, reindex_smul, reindex_map, fDividedPower_one,
    fMatrix_3, fDividedPower_3_two, fDividedPower_3_three]
  simp [negative3, negative3Entries, scalarMatrix, matrix_append, matrix_identity, Matrix.map_add, Matrix.map_one, add_assoc]

lemma trace_simpleMatrices (t u : S) :
    Matrix.trace (positiveMatrix (typeF4RootPairing_baseEquiv 0) t *
      positiveMatrix (typeF4RootPairing_baseEquiv 3) u *
      (negativeMatrix (typeF4RootPairing_baseEquiv 0) (1 : S) *
       negativeMatrix (typeF4RootPairing_baseEquiv 3) (1 : S))) =
      52 + 18 * t + 36 * u + t ^ 2 + 7 * u ^ 2 + 10 * t * u + 2 * t * u ^ 2 := by
  rw [← trace_reindex]
  simp only [map_mul, positiveMatrix_0, positiveMatrix_3, negativeMatrix_0, negativeMatrix_3]
  exact finite_trace t u

end
end ReeF4.Cartan.FieldSeparation.TraceValues
namespace ReeF4.Cartan.FieldSeparation
noncomputable section
open TraceValues
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- The four actual end-root matrices have trace `t² + u²` in characteristic two. -/
theorem endRoot_trace {S : Type*} [CommRing S] [CharP S 2] (t u : S) :
    Matrix.trace ((F4Chevalley.rootCurve (typeF4SimpleRootIndex 0) t *
      F4Chevalley.rootCurve (typeF4SimpleRootIndex 3) u *
      (F4Chevalley.rootCurve (-typeF4SimpleRootIndex 0) (1 : S) *
       F4Chevalley.rootCurve (-typeF4SimpleRootIndex 3) (1 : S))).val) = t ^ 2 + u ^ 2 := by
  simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple, rootCurveUnit_neg_simple,
    Units.val_mul, positiveUnit_val, negativeUnit_val]
  rw [trace_simpleMatrices]
  have h2 : (2 : S) = 0 := CharTwo.two_eq_zero
  calc
    _ = t ^ 2 + u ^ 2 +
        2 * (26 + 9 * t + 18 * u + 3 * u ^ 2 + 5 * t * u + t * u ^ 2) := by ring
    _ = t ^ 2 + u ^ 2 := by rw [h2, zero_mul, add_zero]

/-- The existing fixed-group witness realizes the trace values needed for field separation. -/
theorem traceWitness_trace {m : ℕ} (d : LocalBlockInput m) (t : CoefficientField m) :
    Matrix.trace ((traceWitness d t).val.val : MatrixCarrier m) =
      t ^ 2 + t ^ (2 ^ (m + 1)) := by
  rw [traceWitness_matrix, endRoot_trace]
  rw [← pow_mul, ← pow_succ]
end
end ReeF4.Cartan.FieldSeparation

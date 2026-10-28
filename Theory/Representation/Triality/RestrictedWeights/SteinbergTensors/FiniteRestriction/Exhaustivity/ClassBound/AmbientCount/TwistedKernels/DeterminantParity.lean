module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TwistedKernels.Lattice
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Data.ZMod.Basic

/-!
# Characteristic-two coprimality of twisted torus determinants

Modulo two, `2^n δ* - ρ(w⁻¹)` is the negative of an integral lattice
automorphism. Its determinant is therefore nonzero modulo two. The proof uses
matrix functoriality and the unit determinant of a linear equivalence; no
Weyl-element enumeration is needed. In particular, exponent one is included.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 14.9(b).
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount
open Theory.AlgebraicGroup.StandardRootSystem D4RestrictedWeight

theorem twistedWeightMap_det_odd (ρ : WeightRepresentation) (n : ℕ)
    (hn : 0 < n) (w : Weyl) : Odd (twistedWeightMap ρ (2 ^ n) w).det.natAbs := by
  let b := Pi.basisFun ℤ (Fin 4)
  let r := Int.castRingHom (ZMod 2)
  have htwo : r ((2 : ℤ) ^ n) = 0 := by
    rw [map_pow]
    change (2 : ZMod 2) ^ n = 0
    rw [show (2 : ZMod 2) = 0 by decide, zero_pow (Nat.ne_of_gt hn)]
  have hmat : (LinearMap.toMatrix b b (twistedWeightMap ρ (2 ^ n) w)).map r =
      -(LinearMap.toMatrix b b (ρ w⁻¹).toLinearMap).map r := by
    simp only [twistedWeightMap, map_sub, map_smul]
    ext i j
    change r ((2 ^ n : ℤ) * _ - _) = - r _
    rw [map_sub, map_mul, htwo, zero_mul, zero_sub]
  have hdet : r (twistedWeightMap ρ (2 ^ n) w).det =
      r (ρ w⁻¹).toLinearMap.det := by
    rw [← LinearMap.det_toMatrix b, r.map_det]
    change ((LinearMap.toMatrix b b (twistedWeightMap ρ (2 ^ n) w)).map r).det = _
    rw [hmat, Matrix.det_neg]
    rw [show (-1 : ZMod 2) ^ Fintype.card (Fin 4) = 1 by decide, one_mul]
    change (r.mapMatrix (LinearMap.toMatrix b b (ρ w⁻¹).toLinearMap)).det =
      r (ρ w⁻¹).toLinearMap.det
    rw [← r.map_det, LinearMap.det_toMatrix]
  have hne : r (twistedWeightMap ρ (2 ^ n) w).det ≠ 0 := by
    rw [hdet]
    exact ((ρ w⁻¹).isUnit_det'.map r).ne_zero
  apply Odd.natAbs
  apply Int.not_even_iff_odd.mp
  intro heven
  exact hne (ZMod.intCast_eq_zero_iff_even.mpr heven)
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount

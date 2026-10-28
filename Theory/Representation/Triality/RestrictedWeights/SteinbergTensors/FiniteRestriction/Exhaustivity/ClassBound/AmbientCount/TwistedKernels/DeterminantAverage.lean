module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TwistedKernels.Lattice
public import Mathlib.LinearAlgebra.Determinant

/-!
# The signed D4 Weyl determinant average

For every compatible action on the integral weight lattice and every integral
endomorphism `f`, the sum of `det (f - ρ(w))` is `|W| det f`. Specializing to
`f = q δ*` gives `q⁴ |W|`, for every integer `q`, including `q = 2`.

The proof pairs summands under four actual Weyl elements. The three arm
reflections and the reflection word for the highest root negate independent
coordinates `(a₀, a₂, a₃, a₀ + 2a₁ + a₂ + a₃)`. Determinant multilinearity
successively removes each row involving `ρ(w)`. This coordinate map has
integral determinant two; cancelling that factor returns to the given lattice.
Reindexing by inversion preserves the contravariant convention in
`twistedWeightMap`. No Weyl-group enumeration, determinant sign, or kernel
cardinality is used.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 14.4 and 14.5(a), as used
in 14.8(a).
-/

public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount

open Theory.AlgebraicGroup.StandardRootSystem D4RestrictedWeight

/-- Pairing under independent row sign changes removes every varying row. -/
private theorem sum_det_of_row_signs {G I : Type*} [Group G] [Fintype G]
    [Fintype I] [DecidableEq I] (A : Matrix I I ℤ) (B : G → Matrix I I ℤ)
    (hB : ∀ i, ∃ r : G, ∀ w k j,
      B (r * w) k j = if k = i then -B w k j else B w k j) :
    (∑ w, (A - B w).det) = Fintype.card G * A.det := by
  classical
  let M (s : Finset I) (w : G) : Matrix I I ℤ :=
    fun k j => A k j - if k ∈ s then B w k j else 0
  have hs (s : Finset I) : (∑ w, (M s w).det) = Fintype.card G * A.det := by
    induction s using Finset.induction_on with
    | empty => simp [M]
    | @insert i s hi ih =>
      obtain ⟨r, hr⟩ := hB i
      have hp (w : G) : (M (insert i s) w).det + (M (insert i s) (r * w)).det =
          2 * (M s w).det := by
        have h₁ : M (insert i s) w = (M s w).updateRow i (A i - B w i) := by
          ext k j
          by_cases hk : k = i <;> simp [Matrix.updateRow, M, hk]
        have h₂ : M (insert i s) (r * w) =
            (M s w).updateRow i (A i + B w i) := by
          ext k j
          by_cases hk : k = i <;> simp [Matrix.updateRow, M, hk, hr]
        rw [h₁, h₂, ← Matrix.det_updateRow_add]
        have hu : (A i - B w i) + (A i + B w i) = (2 : ℤ) • A i := by
          ext j
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [hu, Matrix.det_updateRow_smul]
        have hrow : A i = M s w i := by ext j; simp [M, hi]
        rw [hrow, Matrix.updateRow_eq_self]
      have he := Equiv.sum_comp (Equiv.mulLeft r) (fun w => (M (insert i s) w).det)
      change (∑ w, (M (insert i s) (r * w)).det) = _ at he
      have ht := congrArg (fun f : G → ℤ => ∑ w, f w) (funext hp)
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at ht
      change (∑ w, (M (insert i s) w).det) + (∑ w, (M (insert i s) (r * w)).det) =
        2 * ∑ w, (M s w).det at ht
      rw [he, ih] at ht
      omega
  change (∑ w, Matrix.det (fun k j => A k j - B w k j)) = _
  simpa [M] using hs Finset.univ

/-- Pairings with the three arms and the highest coroot. -/
private def coordinates : Weight →ₗ[ℤ] Weight where
  toFun a := ![a 0, a 2, a 3, a 0 + 2 * a 1 + a 2 + a 3]
  map_add' a b := by
    ext i
    fin_cases i <;> simp
    ring
  map_smul' c a := by
    ext i
    fin_cases i <;> simp
    ring

private def simple (i : Fin 4) : Weyl :=
  RootPairing.weylGroup.ofIdx (typeDRootPairing 2) (typeDSimpleRootIndex 2 i)

/-- Actual Weyl words, with the highest-root reflection last. -/
private def orthogonalReflection (i : Fin 4) : Weyl :=
  ![simple 0, simple 2, simple 3,
    simple 1 * simple 0 * simple 2 * simple 3 * simple 1 *
      simple 3 * simple 2 * simple 0 * simple 1] i

private theorem reflection_formula (i : Fin 4) (a : Weight) :
    reflection i a =
      ![![-a 0, a 1 + a 0, a 2, a 3],
        ![a 0 + a 1, -a 1, a 2 + a 1, a 3 + a 1],
        ![a 0, a 1 + a 2, -a 2, a 3],
        ![a 0, a 1 + a 3, a 2, -a 3]] i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [reflection, typeDCartanMatrix] <;> ring

private theorem coordinates_reflection (ρ : WeightRepresentation)
    (hρ : ReflectionCompatible ρ) (i k : Fin 4) (a : Weight) :
    coordinates (ρ (orthogonalReflection i) a) k =
      if k = i then -coordinates a k else coordinates a k := by
  have hr (j : Fin 4) (b : Weight) : ρ (simple j) b = reflection j b := hρ j b
  fin_cases i <;> fin_cases k <;>
    simp [orthogonalReflection, map_mul, LinearEquiv.mul_apply, hr,
      reflection_formula, coordinates] <;> ring

private theorem coordinates_det : coordinates.det = 2 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℤ (Fin 4))]
  have hm : LinearMap.toMatrix (Pi.basisFun ℤ (Fin 4)) (Pi.basisFun ℤ (Fin 4))
      coordinates = !![1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 1, 2, 1, 1] := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
    fin_cases i <;> fin_cases j <;> decide
  rw [hm]
  norm_num [Matrix.det_succ_row_zero, Matrix.det_fin_three, Fin.sum_univ_succ,
    Matrix.submatrix]
  decide

/-- The integral D4 specialization of the endomorphism average in 14.5(a). -/
theorem sum_det_sub_weightRepresentation (ρ : WeightRepresentation)
    (hρ : ReflectionCompatible ρ) (f : Weight →ₗ[ℤ] Weight) :
    (∑ w : Weyl, (f - (ρ w).toLinearMap).det) =
      f.det * (Nat.card Weyl : ℤ) := by
  let b := Pi.basisFun ℤ (Fin 4)
  let A := LinearMap.toMatrix b b (coordinates.comp f)
  let B (w : Weyl) := LinearMap.toMatrix b b (coordinates.comp (ρ w).toLinearMap)
  have hB : ∀ i, ∃ r : Weyl, ∀ w k j,
      B (r * w) k j = if k = i then -B w k j else B w k j := by
    intro i
    refine ⟨orthogonalReflection i, ?_⟩
    intro w k j
    simp only [B, b, LinearMap.toMatrix_apply, Pi.basisFun_repr,
      LinearMap.comp_apply, LinearEquiv.coe_coe, map_mul, LinearEquiv.mul_apply]
    exact coordinates_reflection ρ hρ i k (ρ w (b j))
  have ht := sum_det_of_row_signs A B hB
  have hd (w : Weyl) : (A - B w).det = 2 * (f - (ρ w).toLinearMap).det := by
    rw [← coordinates_det, ← LinearMap.det_comp, ← LinearMap.det_toMatrix b]
    congr 1
    simp only [A, B, LinearMap.comp_sub, map_sub]
  have ha : A.det = 2 * f.det := by
    change (LinearMap.toMatrix b b (coordinates.comp f)).det = _
    rw [LinearMap.det_toMatrix, LinearMap.det_comp, coordinates_det]
  simp_rw [hd] at ht
  rw [← Finset.mul_sum, ha, ← Nat.card_eq_fintype_card] at ht
  nlinarith

private theorem diagram_det : diagramWeightMap.det = 1 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℤ (Fin 4))]
  have hm : LinearMap.toMatrix (Pi.basisFun ℤ (Fin 4)) (Pi.basisFun ℤ (Fin 4))
      diagramWeightMap = !![0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0] := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
    fin_cases i <;> fin_cases j <;> decide
  rw [hm]
  norm_num [Matrix.det_succ_row_zero, Matrix.det_fin_three, Fin.sum_univ_succ,
    Matrix.submatrix]
  decide

/-- The signed twisted determinant average for every integer parameter.
In particular, `q = 2^n` requires no exclusion of exponent one. -/
theorem sum_twistedWeightMap_det (ρ : WeightRepresentation)
    (hρ : ReflectionCompatible ρ) (q : ℤ) :
    (∑ w : Weyl, (twistedWeightMap ρ q w).det) = q ^ 4 * (Nat.card Weyl : ℤ) := by
  calc
    _ = ∑ w : Weyl, (q • diagramWeightMap - (ρ w).toLinearMap).det := by
      exact Equiv.sum_comp (Equiv.inv Weyl)
        (fun w => (q • diagramWeightMap - (ρ w).toLinearMap).det)
    _ = (q • diagramWeightMap).det * (Nat.card Weyl : ℤ) :=
      sum_det_sub_weightRepresentation ρ hρ _
    _ = _ := by
      rw [LinearMap.det_smul, diagram_det, mul_one]
      simp

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount

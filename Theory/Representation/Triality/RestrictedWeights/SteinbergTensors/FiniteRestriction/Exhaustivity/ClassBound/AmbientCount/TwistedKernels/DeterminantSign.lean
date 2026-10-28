module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TwistedKernels.Lattice
public import Theory.AlgebraicGroup.RootSystems.AffinePath
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Positive determinants for the D4 graph-field twist

In simple-coroot coordinates, four times the Euclidean squared norm is
`(2a₀ + 2a₁ + a₂ + a₃)² + (2a₁ + a₂ + a₃)² + (a₂ + a₃)² + (−a₂ + a₃)²`.
The numbered simple reflections and the diagram cycle preserve this positive
form. Simple-reflection word generation therefore gives its invariance under
any reflection-compatible Weyl representation.

For real `q > 1`, the matrices `q δ* − t ρ(w)` are nonsingular throughout
`0 ≤ t ≤ 1`: a nonzero kernel vector would have squared norm multiplied by
both `q²` and `t²`. Their determinants consequently keep the positive sign of
`det(q δ*) = q⁴`. Casting the integral matrices to the reals proves the
requested positivity for every positive field exponent, including one.

This is the D4 graph-field case of Steinberg's sign argument in
`refs/KGroup/GLS3/Chapter2St2.tex`, Lemma 14.9(a).
-/

public noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount
private def realMatrix (f : Weight →ₗ[ℤ] Weight) : Matrix (Fin 4) (Fin 4) ℝ :=
  (LinearMap.toMatrix' f).map (Int.castRingHom ℝ)

private lemma realMatrix_mul (f g : Weight →ₗ[ℤ] Weight) :
    realMatrix (f * g) = realMatrix f * realMatrix g := by
  unfold realMatrix
  rw [LinearMap.toMatrix'_mul]
  exact Matrix.map_mul

/-- Four times the Euclidean squared norm in simple-coroot coordinates. -/
private def normSq (a : Fin 4 → ℝ) : ℝ :=
  (2*a 0 + 2*a 1 + a 2 + a 3)^2 + (2*a 1 + a 2 + a 3)^2 +
    (a 2 + a 3)^2 + (-a 2 + a 3)^2

private lemma normSq_pos {a : Fin 4 → ℝ} (ha : a ≠ 0) : 0 < normSq a := by
  have h0 := sq_nonneg (2*a 0 + 2*a 1 + a 2 + a 3)
  have h1 := sq_nonneg (2*a 1 + a 2 + a 3)
  have h2 := sq_nonneg (a 2 + a 3)
  have h3 := sq_nonneg (-a 2 + a 3)
  by_contra h
  have hz : normSq a = 0 := by dsimp [normSq] at *; linarith
  have hz0 : 2*a 0 + 2*a 1 + a 2 + a 3 = 0 := by
    have : (2*a 0 + 2*a 1 + a 2 + a 3)^2 = 0 := by dsimp [normSq] at hz; linarith
    nlinarith
  have hz1 : 2*a 1 + a 2 + a 3 = 0 := by
    have : (2*a 1 + a 2 + a 3)^2 = 0 := by dsimp [normSq] at hz; linarith
    nlinarith
  have hz2 : a 2 + a 3 = 0 := by
    have : (a 2 + a 3)^2 = 0 := by dsimp [normSq] at hz; linarith
    nlinarith
  have hz3 : -a 2 + a 3 = 0 := by
    have : (-a 2 + a 3)^2 = 0 := by dsimp [normSq] at hz; linarith
    nlinarith
  apply ha
  funext i
  fin_cases i
  · change a 0 = 0; linarith
  · change a 1 = 0; linarith
  · change a 2 = 0; linarith
  · change a 3 = 0; linarith

private lemma normSq_smul (t : ℝ) (a : Fin 4 → ℝ) :
    normSq (t • a) = t^2 * normSq a := by
  simp only [normSq, Pi.smul_apply, smul_eq_mul]
  ring

private lemma realMatrix_reflection (ρ : WeightRepresentation) (hρ : ReflectionCompatible ρ)
    (i : Fin 4) (a : Fin 4 → ℝ) :
    (realMatrix (ρ (RootPairing.weylGroup.ofIdx (typeDRootPairing 2)
      (typeDSimpleRootIndex 2 i))).toLinearMap).mulVec a =
      fun j => a j - a i * (typeDCartanMatrix 2 i j : ℝ) := by
  ext j
  change ∑ k : Fin 4, (↑((ρ (RootPairing.weylGroup.ofIdx (typeDRootPairing 2)
    (typeDSimpleRootIndex 2 i))) (Pi.single k 1) j) : ℝ) * a k = _
  simp_rw [hρ i, reflection]
  simp [Pi.single_apply, sub_mul, Finset.sum_sub_distrib, ite_mul]
  exact mul_comm _ _

private lemma normSq_reflection (i : Fin 4) (a : Fin 4 → ℝ) :
    normSq (fun j => a j - a i * (typeDCartanMatrix 2 i j : ℝ)) = normSq a := by
  fin_cases i <;> norm_num [normSq, typeDCartanMatrix, Fin.ext_iff] <;> ring!

/-- Invariance extends from the four simple reflections to every Weyl word. -/
private lemma normSq_weyl (ρ : WeightRepresentation) (hρ : ReflectionCompatible ρ)
    (w : Weyl) (a : Fin 4 → ℝ) :
    normSq ((realMatrix (ρ w).toLinearMap).mulVec a) = normSq a := by
  obtain ⟨l, rfl⟩ := (typeDRootPairing_base 2).exists_wordProd_eq w
  induction l generalizing a with
  | nil => simp [realMatrix]
  | cons i l ih =>
    obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective i
    rw [RootPairing.Base.wordProd_cons, map_mul]
    change normSq ((realMatrix ((ρ _).toLinearMap * (ρ _).toLinearMap)).mulVec a) = _
    rw [realMatrix_mul, ← Matrix.mulVec_mulVec]
    rw [show (typeDRootPairing_base 2).simpleReflection (typeDRootPairing_baseEquiv 2 i) =
      RootPairing.weylGroup.ofIdx (typeDRootPairing 2) (typeDSimpleRootIndex 2 i) by
        simp [RootPairing.Base.simpleReflection]]
    rw [realMatrix_reflection ρ hρ, normSq_reflection, ih]

private lemma realMatrix_diagram (a : Fin 4 → ℝ) :
    (realMatrix diagramWeightMap).mulVec a = a ∘ typeD4DiagramPermutation := by
  ext i
  change ∑ k : Fin 4, (((Pi.single k (1 : ℤ) : Fin 4 → ℤ) (typeD4DiagramPermutation i)) : ℝ) * a k = _
  simp [Pi.single_apply, ite_mul]

private lemma normSq_diagram (a : Fin 4 → ℝ) :
    normSq ((realMatrix diagramWeightMap).mulVec a) = normSq a := by
  rw [realMatrix_diagram]
  simp [normSq, typeD4DiagramPermutation]
  ring

private lemma realMatrix_diagram_det : (realMatrix diagramWeightMap).det = 1 := by
  have hm : realMatrix diagramWeightMap =
      (1 : Matrix (Fin 4) (Fin 4) ℝ).submatrix typeD4DiagramPermutation id := by
    ext i j
    simp only [realMatrix, Matrix.map_apply, LinearMap.toMatrix'_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [diagramWeightMap, typeD4DiagramPermutation, Matrix.submatrix,
        Matrix.one_apply, Pi.single_apply, Fin.ext_iff]
  rw [hm, Matrix.det_permute, Matrix.det_one, mul_one]
  have hs : Equiv.Perm.sign typeD4DiagramPermutation = 1 := by decide +kernel
  simp [hs]

/-- The contraction of the Weyl term never introduces a kernel vector. -/
private lemma homotopy_det_ne_zero (ρ : WeightRepresentation) (hρ : ReflectionCompatible ρ)
    (w : Weyl) (q t : ℝ) (hq : 1 < q) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (q • realMatrix diagramWeightMap - t • realMatrix (ρ w).toLinearMap).det ≠ 0 := by
  intro hz
  obtain ⟨a, ha, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, sub_eq_zero] at hker
  have hnorm := congrArg normSq hker
  rw [normSq_smul, normSq_smul, normSq_diagram, normSq_weyl ρ hρ] at hnorm
  have hapos := normSq_pos ha
  have hqt : t^2 < q^2 := by nlinarith [ht.1, ht.2]
  nlinarith

private lemma real_det_pos (ρ : WeightRepresentation) (hρ : ReflectionCompatible ρ)
    (w : Weyl) (q : ℝ) (hq : 1 < q) :
    (q • realMatrix diagramWeightMap - realMatrix (ρ w).toLinearMap).det > 0 := by
  let f : ℝ → ℝ := fun t =>
    (q • realMatrix diagramWeightMap - t • realMatrix (ρ w).toLinearMap).det
  have hf : Continuous f :=
    (continuous_const.sub (continuous_id.smul continuous_const)).matrix_det
  have hf0 : 0 < f 0 := by
    simp only [f, zero_smul, sub_zero, Matrix.det_smul, realMatrix_diagram_det,
      Fintype.card_fin, mul_one]
    positivity
  have hf1 : f 1 =
      (q • realMatrix diagramWeightMap - realMatrix (ρ w).toLinearMap).det := by
    simp [f]
  rw [← hf1]
  by_contra h
  have hle : f 1 ≤ 0 := le_of_not_gt h
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num)
    hf.continuousOn ⟨hle, hf0.le⟩
  exact homotopy_det_ne_zero ρ hρ w q t hq ht hzero

private lemma realMatrix_twisted (ρ : WeightRepresentation) (q : ℤ) (w : Weyl) :
    realMatrix (twistedWeightMap ρ q w) =
      (q : ℝ) • realMatrix diagramWeightMap - realMatrix (ρ w⁻¹).toLinearMap := by
  ext i j
  simp [realMatrix, twistedWeightMap, LinearMap.toMatrix'_apply]

private lemma realMatrix_det (f : Weight →ₗ[ℤ] Weight) :
    (realMatrix f).det = (f.det : ℝ) := by
  change ((Int.castRingHom ℝ).mapMatrix (LinearMap.toMatrix' f)).det = _
  rw [← RingHom.map_det, LinearMap.det_toMatrix']
  rfl

/-- The integral D4 twisted determinant is positive for every positive field
exponent, including `n = 1`, for any reflection-compatible weight action. -/
theorem twistedWeightMap_det_pos (ρ : WeightRepresentation) (hρ : ReflectionCompatible ρ)
    (n : ℕ) (hn : 0 < n) (w : Weyl) : 0 < (twistedWeightMap ρ ((2 : ℤ) ^ n) w).det := by
  have hq : (1 : ℝ) < ((2 : ℤ) ^ n : ℤ) := by
    exact_mod_cast one_lt_pow₀ (show (1 : ℤ) < 2 by norm_num) (Nat.ne_of_gt hn)
  have h := real_det_pos ρ hρ w⁻¹ ((2 : ℤ) ^ n : ℤ) hq
  rw [← realMatrix_twisted, realMatrix_det] at h
  exact_mod_cast h

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount

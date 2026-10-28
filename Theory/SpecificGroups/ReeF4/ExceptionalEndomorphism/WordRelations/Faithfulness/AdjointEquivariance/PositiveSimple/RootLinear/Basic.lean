module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.Coefficients
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Relations

/-!
# Root-column reduction of the positive-simple commutator

The first divided power has three kinds of root columns: a root-string
multiple when the sum is a root, the simple Cartan vector at the opposite
simple root, and zero otherwise. Applying the fixed adjoint map gives the
corresponding three formulas for `columnImage`.

The opposite-root identity follows directly from the definition of the Cartan
operator. For the other negative simple roots, Geck's relation
`[e_i, f_j] = 0` proves the operator identity. The identical positive simple
root is also handled here. The remaining root-sum and vanishing operator
commutators are separate obligations; vector-action formulas alone do not
establish them.

Sources: Geck's integral root-string construction, implemented in
`IntegralGeckConstruction` and `IntegralAllRootOperators`, and Geck (2017),
Lemma 3.5, implemented in Mathlib's `GeckConstruction.Relations`.
-/

public section

open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
noncomputable section

private lemma cast_mulVec (m : ℕ) (A : Matrix Coordinate Coordinate ℤ) (v : Coordinate → ℤ) :
    (Int.castRingHom (CoefficientField m)) ∘ (A *ᵥ v) =
      A.map (Int.castRingHom (CoefficientField m)) *ᵥ
        ((Int.castRingHom (CoefficientField m)) ∘ v) := by
  ext x
  exact (Int.castRingHom (CoefficientField m)).map_mulVec A v x

private lemma cast_single (m : ℕ) (j : Coordinate) :
    (Int.castRingHom (CoefficientField m)) ∘ Pi.single j (1 : ℤ) = Pi.single j 1 := by
  classical
  ext x
  by_cases h : x = j <;> simp [h]

/-- The opposite-simple column maps to the prescribed simple Cartan operator. -/
lemma columnImage_one_neg_simple (m : ℕ) (i : typeF4RootPairing_base.support) :
    let := typeF4RootPairing.indexNeg
    columnImage m i 1 (Sum.inr (-(i : typeF4Roots))) =
      coordinateOperator m (Sum.inl i) := by
  let := typeF4RootPairing.indexNeg
  have h := congrArg (fun v : Coordinate → ℤ =>
    (Int.castRingHom (CoefficientField m)) ∘ v)
    (eMatrix_mulVec_v_neg (P := typeF4RootPairing) i)
  simp only [cast_mulVec, v, u, cast_single] at h
  unfold columnImage
  have hd : dividedPower m i 1 =
      (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField m)) := by
    simp [dividedPower]
  rw [hd]
  change adjointMap m (((eMatrix (P := typeF4RootPairing) i).map
    (Int.castRingHom (CoefficientField m))).col (Sum.inr (-i.val))) = _
  rw [← Matrix.mulVec_single_one, h, adjointMap_single]

/-- The canonical negative-simple route gives the actual negative Geck operator. -/
lemma coordinateOperator_negative_simple (m : ℕ) (i : typeF4RootPairing_base.support) :
    let := typeF4RootPairing.indexNeg
    coordinateOperator m (Sum.inr (-(i : typeF4Roots))) =
      (fMatrix (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField m)) := by
  let := typeF4RootPairing.indexNeg
  change (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-i.val)).map _ = _
  rw [rootOperator_neg_simple]

/-- The opposite root satisfies the degree-one identity without further premises. -/
lemma positive_root_coefficient_one_opposite (m : ℕ) (i : typeF4RootPairing_base.support) :
    let := typeF4RootPairing.indexNeg
    CoefficientIdentity m i (Sum.inr (-(i : typeF4Roots))) 1 := by
  let := typeF4RootPairing.indexNeg
  rw [coefficientIdentity_one_iff, columnImage_one_neg_simple,
    coordinateOperator_negative_simple]
  simp only [coordinateOperator, dividedPower, eDividedPower_one]

/-- The first positive divided power is the actual positive-simple root operator. -/
lemma dividedPower_one_eq_coordinateOperator (m : ℕ)
    (i : typeF4RootPairing_base.support) :
    dividedPower m i 1 = coordinateOperator m (Sum.inr i) := by
  change _ = (rootOperator (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) i).map _
  simp [dividedPower]

/-- A root-sum column maps to its root-string multiple of the actual sum-root operator. -/
lemma columnImage_one_root_add (m : ℕ) (i : typeF4RootPairing_base.support)
    (r s : typeF4Roots)
    (h : typeF4RootPairing.root s = typeF4RootPairing.root i + typeF4RootPairing.root r) :
    columnImage m i 1 (Sum.inr r) =
      (typeF4RootPairing.chainBotCoeff i r + 1 : CoefficientField m) •
        coordinateOperator m (Sum.inr s) := by
  have he := congrArg (fun v : Coordinate → ℤ =>
    (Int.castRingHom (CoefficientField m)) ∘ v)
    (eMatrix_mulVec_v_add (P := typeF4RootPairing) h)
  have hs (z : ℤ) (v : Coordinate → ℤ) :
      (Int.castRingHom (CoefficientField m)) ∘ (z • v) =
        (z : CoefficientField m) • ((Int.castRingHom (CoefficientField m)) ∘ v) := by
    ext x
    simp
  simp only [cast_mulVec, hs, v, cast_single, Int.cast_add,
    Int.cast_natCast, Int.cast_one] at he
  unfold columnImage
  simp only [dividedPower, eDividedPower_one]
  change adjointMap m (((eMatrix (P := typeF4RootPairing) i).map
    (Int.castRingHom (CoefficientField m))).col (Sum.inr r)) = _
  rw [← Matrix.mulVec_single_one, he, map_smul, adjointMap_single]

/-- A non-opposite column maps to zero when the root sum is absent. -/
lemma columnImage_one_root_zero (m : ℕ) (i : typeF4RootPairing_base.support)
    (r : typeF4Roots) (hopp : letI := typeF4RootPairing.indexNeg; r ≠ -(i : typeF4Roots))
    (h : typeF4RootPairing.root i + typeF4RootPairing.root r ∉
      Set.range typeF4RootPairing.root) : columnImage m i 1 (Sum.inr r) = 0 := by
  have he := congrArg (fun v : Coordinate → ℤ =>
    (Int.castRingHom (CoefficientField m)) ∘ v)
    (eMatrix_mulVec_v_zero (P := typeF4RootPairing) hopp h)
  simp only [cast_mulVec, v, cast_single] at he
  have hz : (Int.castRingHom (CoefficientField m)) ∘ (0 : Coordinate → ℤ) = 0 := by
    ext x
    simp
  rw [hz] at he
  unfold columnImage
  simp only [dividedPower, eDividedPower_one]
  change adjointMap m (((eMatrix (P := typeF4RootPairing) i).map
    (Int.castRingHom (CoefficientField m))).col (Sum.inr r)) = _
  rw [← Matrix.mulVec_single_one, he, map_zero]

/-- The identical simple root satisfies the degree-one identity. -/
lemma positive_root_coefficient_one_same (m : ℕ) (i : typeF4RootPairing_base.support) :
    CoefficientIdentity m i (Sum.inr (i : typeF4Roots)) 1 := by
  have hz : columnImage m i 1 (Sum.inr (i : typeF4Roots)) = 0 := by
    apply columnImage_one_root_zero m i i
    · exact RootPairing.ne_neg typeF4RootPairing i
    · intro hmem
      have : (2 : ℕ).AtLeastTwo := ⟨by omega⟩
      apply typeF4RootPairing.nsmul_notMem_range_root (n := 2) (i := i)
      simpa [two_smul] using hmem
  rw [coefficientIdentity_one_iff, hz, dividedPower_one_eq_coordinateOperator, sub_self]

private lemma integral_simple_commutator_ne (i j : typeF4RootPairing_base.support)
    (hij : i ≠ j) :
    eMatrix (P := typeF4RootPairing) i * fMatrix j -
      fMatrix j * eMatrix i = 0 := by
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ ℝ)
  simpa only [Ring.lie_def, Matrix.map_sub _ (map_sub _), Matrix.map_mul, map_eMatrix,
    map_fMatrix, Matrix.map_zero _ (map_zero _)] using
    (RootPairing.GeckConstruction.lie_e_f_ne (P := typeF4RootPairing) hij)

/-- Every negative simple root satisfies the degree-one identity. -/
lemma positive_root_coefficient_one_negative_simple (m : ℕ)
    (i j : typeF4RootPairing_base.support) :
    letI := typeF4RootPairing.indexNeg
    CoefficientIdentity m i (Sum.inr (-(j : typeF4Roots))) 1 := by
  let := typeF4RootPairing.indexNeg
  by_cases hij : i = j
  · subst j
    exact positive_root_coefficient_one_opposite m i
  rw [coefficientIdentity_one_iff, columnImage_one_root_zero]
  · rw [coordinateOperator_negative_simple]
    simp only [dividedPower, eDividedPower_one]
    have h := congrArg (fun A : Matrix Coordinate Coordinate ℤ =>
      A.map (Int.castRingHom (CoefficientField m))) (integral_simple_commutator_ne i j hij)
    simpa only [Matrix.map_sub _ (map_sub _), Matrix.map_mul,
      Matrix.map_zero _ (map_zero _)] using h.symm
  · exact fun h => hij (Subtype.ext (neg_injective h).symm)
  · simpa only [RootPairing.indexNeg_neg, typeF4RootPairing.root_reflectionPerm,
      typeF4RootPairing.reflection_apply_self, ← sub_eq_add_neg] using
      typeF4RootPairing_base.sub_notMem_range_root i.property j.property

end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple

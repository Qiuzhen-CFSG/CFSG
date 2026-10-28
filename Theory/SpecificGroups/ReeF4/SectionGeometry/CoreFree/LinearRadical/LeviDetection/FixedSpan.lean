module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection.FirstLayer
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.RootPartition
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.MatrixRelations

/-!
# Spanning the first matrix layer by fixed Ree radical words

The roots of middle degree one are precisely `0100`, `0010`, `1100`, and
`0011`. They form the first two roots of the B₂ quartets starting at rows
8 and 16 of `RootPartition.table`. The actual fixed words with parameters
`quartetSolution m a 0` belong to the linear radical, and their degree-one
parts are `a • X + halfFrobenius m a • Y` for the corresponding root operators.

For `m ≥ 1`, the coefficient field contains an element outside `{0, 1}`.
Such an element cannot be fixed by half-Frobenius: the inverse Tits map and
the square identity would force `a² = a`. The words at parameters `1` and
`a` therefore span both operators. These two quartets exhaust the required
roots and establish the spanning input to full linear Levi detection.

Source: the root-defined radical and Levi decomposition in GLS3,
Theorem 2.6.5(e,g), `refs/KGroup/GLS3/chapter2.tex`; the concrete fixed-block
relations are proved in `ParabolicAmalgam/RadicalOrders/FixedCoordinates`.
-/

noncomputable section
namespace ReeF4.SectionGeometry.LinearRadical.LeviDetection
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics LargeLocalSeeds Parabolics.RadicalCoordinates.FixedCoordinates

private def quartetRoot (i j : Fin 4) : F4Chevalley.Root :=
  ((rootBlocks (.radical .linear)).roots (.inr (i, j))).val

private theorem quartetRoot_radical (i j : Fin 4) :
    IsRadicalRoot .linear (quartetRoot i j) :=
  ((rootBlocks (.radical .linear)).roots (.inr (i, j))).property

private theorem quartetRoot_degree (i j : Fin 4) (hi : i = 0 ∨ i = 2) :
    rootDegree (quartetRoot i j) = ![1, 1, 2, 3] j := by
  have h := rootDegree_eq (quartetRoot i j)
  simp only [quartetRoot, rootBlocks_roots_val, RootPartition.table_simpleCoefficient] at h
  rcases hi with rfl | rfl <;> fin_cases j <;>
    norm_num [RootPartition.index, RootPartition.quartetRow, RootPartition.coefficients,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;> exact_mod_cast h

private theorem degree_nonneg_of_positive (r : F4Chevalley.Root)
    (hp : typeF4RootPairing_base.IsPos r) : 0 ≤ rootDegree r := by
  obtain ⟨i, hi⟩ := RootPartition.table_exhaustive r hp
  have h := rootDegree_eq r
  rw [← hi, RootPartition.table_simpleCoefficient, RootPartition.table_simpleCoefficient] at h
  have hnonneg : (0 : ℝ) ≤ (rootDegree r : ℝ) := by rw [h]; positivity
  exact_mod_cast hnonneg

private theorem positive_of_degree_one (r : F4Chevalley.Root) (hr : rootDegree r = 1) :
    typeF4RootPairing_base.IsPos r := by
  classical
  by_contra hn
  let := typeF4RootPairing.indexNeg
  have h := degree_nonneg_of_positive (-r)
    ((RootPairing.Base.IsPos.neg_iff_not _ r).mpr hn)
  have hv : (-r).val = -r.val := by
    change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  have he : (rootDegree (-r) : ℝ) = -(rootDegree r : ℝ) := by
    rw [rootDegree_eq, rootDegree_eq, hv]
    simp [typeF4SimpleCoefficient, Pi.neg_apply]
    ring
  have hreal : (0 : ℝ) ≤ (rootDegree (-r) : ℝ) := by exact_mod_cast h
  rw [he, hr] at hreal
  norm_num at hreal

private theorem degree_one_exhaustive (r : F4Chevalley.Root) (hr : rootDegree r = 1) :
    ∃ i j : Fin 4, (i = 0 ∨ i = 2) ∧ (j = 0 ∨ j = 1) ∧ r = quartetRoot i j := by
  obtain ⟨i, hi⟩ := RootPartition.table_exhaustive r (positive_of_degree_one r hr)
  have h := rootDegree_eq r
  rw [hr, ← hi, RootPartition.table_simpleCoefficient, RootPartition.table_simpleCoefficient] at h
  fin_cases i <;>
    norm_num [RootPartition.coefficients, Matrix.cons_val_two, Matrix.cons_val_three] at h
  · refine ⟨0, 0, Or.inl rfl, Or.inl rfl, ?_⟩
    apply Subtype.ext
    rw [quartetRoot, rootBlocks_roots_val]
    exact hi.symm
  · refine ⟨0, 1, Or.inl rfl, Or.inr rfl, ?_⟩
    apply Subtype.ext
    rw [quartetRoot, rootBlocks_roots_val]
    exact hi.symm
  · refine ⟨2, 0, Or.inr rfl, Or.inl rfl, ?_⟩
    apply Subtype.ext
    rw [quartetRoot, rootBlocks_roots_val]
    exact hi.symm
  · refine ⟨2, 1, Or.inr rfl, Or.inr rfl, ?_⟩
    apply Subtype.ext
    rw [quartetRoot, rootBlocks_roots_val]
    exact hi.symm

private theorem quartet_generator_mem (m : ℕ) (i j : Fin 4) (t : CoefficientField m) :
    rootGeneratorInGroup m (quartetRoot i j) t ∈ splitRadical m .linear :=
  Subgroup.subset_closure ⟨_, t, quartetRoot_radical i j, rfl⟩

private theorem quartetWord_mem (m : ℕ) (i : Fin 4) (t : Fin 4 → CoefficientField m) :
    quartetWord m (quartetRoot i) t ∈ splitRadical m .linear := by
  exact (splitRadical m .linear).mul_mem
    ((splitRadical m .linear).mul_mem
      ((splitRadical m .linear).mul_mem (quartet_generator_mem m i 0 _) (quartet_generator_mem m i 1 _))
      (quartet_generator_mem m i 2 _)) (quartet_generator_mem m i 3 _)

private theorem quartetWord_fixed (m : ℕ) (i : Fin 4) (a c : CoefficientField m) :
    reeTwist m (quartetWord m (quartetRoot i) (quartetSolution m a c)) =
      quartetWord m (quartetRoot i) (quartetSolution m a c) := by
  have h := (rootBlocks (.radical .linear)).twist_quartet m
    (mixedRootCommutation m) (b2RootSwap m) i (quartetSolution m a c)
  rw [quartetSolution_fixed] at h
  exact h

private def fixedQuartet (m : ℕ) (i : Fin 4) (a c : CoefficientField m) : Model m :=
  ⟨quartetWord m (quartetRoot i) (quartetSolution m a c),
    (mem_fixedSubgroup m _).mpr (quartetWord_fixed m i a c)⟩

private theorem fixedQuartet_mem (m : ℕ) (i : Fin 4) (a c : CoefficientField m) :
    fixedQuartet m i a c ∈ radical m .linear := by
  change toSplitGroup m (fixedQuartet m i a c) ∈ splitRadical m .linear
  rw [toSplitGroup_apply]
  exact quartetWord_mem m i _

private theorem degreeOnePart_quartetWord (m : ℕ) (i : Fin 4) (hi : i = 0 ∨ i = 2)
    (t : Fin 4 → CoefficientField m) :
    degreeOnePart (quartetWord m (quartetRoot i) t).val.val =
      t 0 • rootOperator m (quartetRoot i 0) + t 1 • rootOperator m (quartetRoot i 1) := by
  have h0 := quartet_generator_mem m i 0 (t 0)
  have h1 := quartet_generator_mem m i 1 (t 1)
  have h2 := quartet_generator_mem m i 2 (t 2)
  have h3 := quartet_generator_mem m i 3 (t 3)
  rw [quartetWord,
    degreeOnePart_split_mul _ _ ((splitRadical m .linear).mul_mem
      ((splitRadical m .linear).mul_mem h0 h1) h2) h3,
    degreeOnePart_split_mul _ _ ((splitRadical m .linear).mul_mem h0 h1) h2,
    degreeOnePart_split_mul _ _ h0 h1,
    degreeOnePart_rootGenerator _ (quartetRoot_degree i 0 hi),
    degreeOnePart_rootGenerator _ (quartetRoot_degree i 1 hi),
    degreeOnePart_rootGenerator_of_one_lt _ (by rw [quartetRoot_degree i 2 hi]; decide),
    degreeOnePart_rootGenerator_of_one_lt _ (by rw [quartetRoot_degree i 3 hi]; decide),
    add_zero, add_zero]

private theorem pairedOperators_mem (m : ℕ) (i : Fin 4) (hi : i = 0 ∨ i = 2)
    (a : CoefficientField m) :
    a • rootOperator m (quartetRoot i 0) + halfFrobenius m a • rootOperator m (quartetRoot i 1)
      ∈ radicalDegreeOneSpan m := by
  apply Submodule.subset_span
  refine ⟨fixedQuartet m i a 0, fixedQuartet_mem m i a 0, ?_⟩
  rw [modelMatrix, toSplitGroup_apply]
  exact (degreeOnePart_quartetWord m i hi (quartetSolution m a 0)).symm

private theorem exists_halfFrobenius_ne (m : ℕ) (hm : 1 ≤ m) :
    ∃ a : CoefficientField m, halfFrobenius m a ≠ a := by
  classical
  have hcard : 2 < Fintype.card (CoefficientField m) := by
    rw [← Nat.card_eq_fintype_card, field_card]
    calc
      2 < 2 ^ 3 := by decide
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hfin : ({0, 1} : Finset (CoefficientField m)).card <
      (Finset.univ : Finset (CoefficientField m)).card := by simpa using hcard
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hfin
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  refine ⟨a, fun he => ?_⟩
  have ht := titsEnd_halfFrobenius m a
  rw [he] at ht
  have hsq := halfFrobenius_sq m a
  rw [he, ht] at hsq
  apply ha.2
  exact mul_left_cancel₀ ha.1 (by simpa [pow_two] using hsq)

private theorem operators_mem (m : ℕ) (hm : 1 ≤ m) (i : Fin 4) (hi : i = 0 ∨ i = 2) :
    rootOperator m (quartetRoot i 0) ∈ radicalDegreeOneSpan m ∧
      rootOperator m (quartetRoot i 1) ∈ radicalDegreeOneSpan m := by
  let S := radicalDegreeOneSpan m
  let X := rootOperator m (quartetRoot i 0)
  let Y := rootOperator m (quartetRoot i 1)
  have hsum : X + Y ∈ S := by simpa using pairedOperators_mem m i hi 1
  obtain ⟨a, ha⟩ := exists_halfFrobenius_ne m hm
  have hpair : a • X + halfFrobenius m a • Y ∈ S := pairedOperators_mem m i hi a
  have hdiff : (halfFrobenius m a - a) • Y ∈ S := by
    convert S.sub_mem hpair (S.smul_mem a hsum) using 1
    module
  have hY : Y ∈ S := by
    have h := S.smul_mem (halfFrobenius m a - a)⁻¹ hdiff
    simpa only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr ha), one_smul] using h
  exact ⟨by simpa using S.sub_mem hsum hY, hY⟩

/-- Every degree-one root operator is in the coefficient-field span of the
degree-one matrices of actual fixed linear radical elements. -/
public theorem rootOperator_mem_radicalDegreeOneSpan (m : ℕ) (hm : 1 ≤ m)
    (r : F4Chevalley.Root) (hr : rootDegree r = 1) :
    rootOperator m r ∈ radicalDegreeOneSpan m := by
  obtain ⟨i, j, hi, hj, rfl⟩ := degree_one_exhaustive r hr
  rcases hj with rfl | rfl
  · exact (operators_mem m hm i hi).1
  · exact (operators_mem m hm i hi).2

end ReeF4.SectionGeometry.LinearRadical.LeviDetection

module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.WeylSeparation.Coordinates
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.Blocks
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.RootCurve

/-!
# Fixed simple-coordinate witnesses in the binary Ree group

The commuting end-root word detects the two end nodes of F₄. For the
middle nodes, write `r = α₁`, `s = α₂`, `c = r+s`, and `d = r+2s`.
The assumed mixed-root commutation and B₂ swap relations make the word
`X_r(1) X_s(1) X_c(1)` fixed under the actual Ree twist: its quartet
parameters are `(1,1,1,0)`, the fixed scalar solution with both free
parameters equal to one.

The integral root grading shows that the degree-one entries of a product
add. Thus the correction factor `X_c(1)` contributes nothing to simple-root
rows of Cartan columns. The integral simple-root operators give entry one
in columns numbered `1,0,3,2` for the four simple roots. All witnesses lie
in the actual twist-fixed positive matrix subgroup.

This is a conditional root calculation, with precisely the two matrix
relations as premises. Their unconditional proofs belong to the separation
assembly. Source: the Chevalley construction underlying Aschbacher–Smith
F.1.12(I)(5), `refs/quasithin.pdf`, printed pp.263–264; integral operators
and positive grading as in Steinberg, *Lectures on Chevalley Groups*.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.Binary.FixedGeometry.WeylSeparation
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup LargeLocalSeeds
open RadicalCoordinates.FixedCoordinates OuterLocal.SuzukiCommutators
open scoped Matrix

private abbrev node := typeF4RootPairing_baseEquiv
private abbrev sr := typeF4SimpleRootIndex
private def c : F4Chevalley.Root := typeF4RootPairing.reflectionPerm (sr 1) (sr 2)
private def d : F4Chevalley.Root := typeF4RootPairing.reflectionPerm (sr 2) (sr 1)

private theorem simple_pos (i : Fin 4) : typeF4RootPairing_base.IsPos (sr i) :=
  typeF4RootPairing_base.isPos_of_mem_support (node i).property

private theorem c_add : c.val = (sr 1).val + (sr 2).val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm (sr 1) (sr 2)) = _
  rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root,
    typeF4RootPairing_simpleIndex_pairing]
  norm_num [typeF4CartanMatrix, Fin.ext_iff, add_comm]

private theorem d_add : d.val = (sr 1).val + (2 : ℝ) • (sr 2).val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm (sr 2) (sr 1)) = _
  rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root,
    typeF4RootPairing_simpleIndex_pairing]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private theorem c_pos : typeF4RootPairing_base.IsPos c :=
  (simple_pos 2).reflectionPerm (node 1).property
    (by intro h; have := typeF4SimpleRootIndex_injective h; contradiction)
private theorem d_pos : typeF4RootPairing_base.IsPos d :=
  (simple_pos 1).reflectionPerm (node 2).property
    (by intro h; have := typeF4SimpleRootIndex_injective h; contradiction)

private theorem c_short : IsShortRoot c := by
  change ¬ IsLongRoot (typeF4RootPairing.reflectionPerm (sr 1) (sr 2))
  rw [WordRelations.isLongRoot_reflection_iff]
  exact (typeF4SimpleRootIndex_mem_pair_iff 2).not.mpr (by decide)

private theorem d_long : IsLongRoot d := by
  rw [d, WordRelations.isLongRoot_reflection_iff]
  exact (typeF4SimpleRootIndex_mem_pair_iff 1).mpr (by decide)

private theorem c_dual : exceptionalRootPermutation c = d := by
  simp only [c, d, WordRelations.exceptionalRootPermutation_reflection,
    exceptionalRootPermutation_simple]
  rfl

private theorem top_dot : dot d.val c.val = 1 := by
  rw [c_add, d_add]
  norm_num [sr, typeF4SimpleRootIndex_val, typeF4SimpleRoot, basisVector, dot,
    Fin.sum_univ_four, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
    Fin.reduceFinMk, Fin.ext_iff]

private theorem middle_fixed (hcomm : MixedRootCommutation 0) (hswap : B2RootSwap 0) :
    reeTwist 0 (quartetWord 0 ![sr 1, sr 2, c, d] (quartetSolution 0 1 1)) =
      quartetWord 0 ![sr 1, sr 2, c, d] (quartetSolution 0 1 1) := by
  rw [reeTwist_quartetWord 0 ![sr 1, sr 2, c, d]
    ((typeF4SimpleRootIndex_mem_pair_iff 1).mpr (by decide)) c_short
    (exceptionalRootPermutation_simple 1) c_dual]
  · rw [quartetSolution_fixed]
  · intro a b
    exact (hcomm d c d_pos c_pos d_long c_short (by rw [top_dot]; norm_num) b a).symm
  · exact hswap (sr 1) (sr 2) c d (simple_pos 1) (simple_pos 2)
      ((typeF4SimpleRootIndex_mem_pair_iff 1).mpr (by decide))
      ((typeF4SimpleRootIndex_mem_pair_iff 2).not.mpr (by decide))
      (by norm_num [sr, typeF4SimpleRootIndex_val, typeF4SimpleRoot, basisVector, dot,
        Fin.sum_univ_four, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
        Fin.reduceFinMk, Fin.ext_iff]) c_add d_add

private def Raises (w : F4Chevalley.BasisIndex → ℤ)
    (A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex (CoefficientField 0)) : Prop :=
  ∀ i j, w i ≤ w j → A i j = 0

private theorem raises_add {w} {A B : Matrix F4Chevalley.BasisIndex
    F4Chevalley.BasisIndex (CoefficientField 0)}
    (hA : Raises w A) (hB : Raises w B) : Raises w (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]

private noncomputable def rootDegree (r : F4Chevalley.Root) : ℤ :=
  11 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 0) +
  21 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 1) +
  15 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 2) +
  8 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 3)

private theorem rootDegree_simple (i : Fin 4) : rootDegree (typeF4SimpleRootIndex i) = 1 := by
  have hp (j : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  simp only [rootDegree, hp]
  fin_cases i <;> norm_num [typeF4CartanMatrix, Fin.ext_iff]

private theorem rootDegree_add {i j k : F4Chevalley.Root}
    (h : typeF4RootPairing.root k = typeF4RootPairing.root i + typeF4RootPairing.root j) :
    rootDegree k = rootDegree i + rootDegree j := by
  have hp (q : F4Chevalley.Root) : typeF4RootPairing.pairingIn ℤ k q =
      typeF4RootPairing.pairingIn ℤ i q + typeF4RootPairing.pairingIn ℤ j q := by
    simpa using typeF4RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ)
      (j := q) (show typeF4RootPairing.root k =
        (1 : ℤ) • typeF4RootPairing.root i + (1 : ℤ) • typeF4RootPairing.root j by simpa using h)
  simp only [rootDegree, hp]
  ring

private noncomputable def basisDegree (a : F4Chevalley.BasisIndex) : ℤ :=
  11 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 0) +
  21 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 1) +
  15 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 2) +
  8 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 3)

private theorem dividedPower_degree (r : F4Chevalley.Root) (n : ℕ)
    (i j : F4Chevalley.BasisIndex)
    (hij : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0) :
    basisDegree i - basisDegree j = (n : ℤ) * rootDegree r := by
  have h := rootDividedPower_isChevalleyHomogeneous (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) r n i j hij
  have h0 := h (typeF4SimpleRootIndex 0)
  have h1 := h (typeF4SimpleRootIndex 1)
  have h2 := h (typeF4SimpleRootIndex 2)
  have h3 := h (typeF4SimpleRootIndex 3)
  dsimp only [basisDegree, rootDegree]
  linear_combination 11 * h0 + 21 * h1 + 15 * h2 + 8 * h3

private theorem dividedPower_low (r : F4Chevalley.Root) (hr : 0 < rootDegree r)
    (n : ℕ) (hn : 0 < n) (i j : F4Chevalley.BasisIndex)
    (hij : basisDegree i < basisDegree j + rootDegree r) :
    specializeMatrix (S := CoefficientField 0)
      (F4Chevalley.integralOperators.rootDividedPower r n) i j = 0 := by
  by_contra hne
  have hint : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0 := by
    intro he
    apply hne
    simp [specializeMatrix, he]
  have hd := dividedPower_degree r n i j hint
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hp : rootDegree r ≤ (n : ℤ) * rootDegree r := by nlinarith
  omega

private theorem rootCurve_low (r : F4Chevalley.Root) (hr : 0 < rootDegree r)
    (t : CoefficientField 0) (i j : F4Chevalley.BasisIndex)
    (hij : basisDegree i < basisDegree j + rootDegree r) :
    ((F4Chevalley.rootCurve r t).val - 1) i j = 0 := by
  rw [F4Chevalley.rootCurve_matrix_formula]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    dividedPower_low r hr 1 (by decide) i j hij,
    dividedPower_low r hr 2 (by decide) i j hij,
    dividedPower_low r hr 3 (by decide) i j hij,
    mul_zero, add_zero, sub_self]

private theorem rootCurve_raises (r : F4Chevalley.Root) (hr : 0 < rootDegree r)
    (t : CoefficientField 0) : Raises basisDegree ((F4Chevalley.rootCurve r t).val - 1) := by
  intro i j hij
  exact rootCurve_low r hr t i j (by omega)

private theorem raises_mul {A B : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex
    (CoefficientField 0)} (hA : Raises basisDegree A) (hB : Raises basisDegree B) :
    Raises basisDegree (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : basisDegree i ≤ basisDegree k
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (by omega), mul_zero]

private theorem raises_unit_mul {A B : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex
    (CoefficientField 0)} (hA : Raises basisDegree (A - 1))
    (hB : Raises basisDegree (B - 1)) : Raises basisDegree (A * B - 1) := by
  have he : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  rw [he]
  exact raises_add (raises_add hA hB) (raises_mul hA hB)

private theorem mul_entry {A B : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex
    (CoefficientField 0)} (hA : Raises basisDegree (A - 1))
    (hB : Raises basisDegree (B - 1)) (i j : F4Chevalley.BasisIndex)
    (hij : basisDegree i = basisDegree j + 1) : (A * B) i j = A i j + B i j := by
  have hne : i ≠ j := by rintro rfl; omega
  have hz : ((A - 1) * (B - 1)) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : basisDegree i ≤ basisDegree k
    · rw [hA i k hik, zero_mul]
    · rw [hB k j (by omega), mul_zero]
  have he : A * B = 1 + (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  rw [he]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero,
    zero_add, hz, add_zero]

private theorem rootDegree_c : rootDegree c = 2 := by
  have h := rootDegree_add (i := sr 1) (j := sr 2) (k := c) c_add
  rw [rootDegree_simple, rootDegree_simple] at h
  exact h

private theorem simple_cartan_degree (i j : Fin 4) :
    basisDegree (.inr (sr i)) = basisDegree (.inl (node j)) + 1 := by
  simpa only [rootDegree, basisDegree, chevalleyBasisWeight, mul_zero, add_zero, zero_add]
    using rootDegree_simple i

private theorem c_entry (i j : Fin 4) :
    (F4Chevalley.rootCurve c (1 : CoefficientField 0)).val (.inr (sr i)) (.inl (node j)) = 0 := by
  have h := rootCurve_low c (by rw [rootDegree_c]; norm_num) 1
    (.inr (sr i)) (.inl (node j)) (by rw [simple_cartan_degree i j, rootDegree_c]; omega)
  simpa only [Matrix.sub_apply, Matrix.one_apply, Sum.inr_ne_inl, ↓reduceIte, sub_zero] using h

private theorem simple_matrix (i : Fin 4) :
    (F4Chevalley.rootCurve (sr i) (1 : CoefficientField 0)).val =
      (eUnipotent (node i) 1).map (Int.castRingHom (CoefficientField 0)) := by
  simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple, positiveUnit_val]
  ext x y
  simp only [eUnipotent, positiveMatrix_formula, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp [Matrix.one_apply]

private theorem simple_entry (i j k : Fin 4) :
    (F4Chevalley.rootCurve (sr i) (1 : CoefficientField 0)).val
      (.inr (sr k)) (.inl (node j)) =
        if k = i then (|typeF4CartanMatrix i j| : ℤ) else 0 := by
  rw [simple_matrix, Matrix.map_apply]
  have h := congrFun (eUnipotent_mulVec_u (node i) (node j) 1) (.inr (sr k))
  have he : sr k = sr i ↔ k = i := typeF4SimpleRootIndex_injective.eq_iff
  simp only [u, v, Matrix.mulVec_single_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    one_mul, Pi.single_apply, Sum.inr_ne_inl, ↓reduceIte, zero_add,
    Matrix.col_apply, Sum.inr.injEq, typeF4RootPairing_baseEquiv_val, he,
    typeF4RootPairing_base_cartan_apply] at h
  rw [h]
  split_ifs <;> simp

private def middleWord : SplitGroup 0 :=
  rootGeneratorInGroup 0 (sr 1) 1 * rootGeneratorInGroup 0 (sr 2) 1 *
    rootGeneratorInGroup 0 c 1

private theorem middleWord_eq : middleWord =
    quartetWord 0 ![sr 1, sr 2, c, d] (quartetSolution 0 1 1) := by
  have hz (r : F4Chevalley.Root) : rootGeneratorInGroup 0 r 0 = 1 :=
    Subtype.ext (F4Chevalley.rootCurve_zero r)
  simp [middleWord, quartetWord, quartetSolution, CharTwo.add_self_eq_zero, hz]

private theorem middleWord_fixed (hcomm : MixedRootCommutation 0) (hswap : B2RootSwap 0) :
    reeTwist 0 middleWord = middleWord := by
  rw [middleWord_eq]
  exact middle_fixed hcomm hswap

private theorem middleWord_mem : middleWord ∈ splitUnipotent 0 := by
  apply Subgroup.mul_mem
  · exact Subgroup.mul_mem _
      (Subgroup.subset_closure ⟨sr 1, 1, simple_pos 1, rfl⟩)
      (Subgroup.subset_closure ⟨sr 2, 1, simple_pos 2, rfl⟩)
  · exact Subgroup.subset_closure ⟨c, 1, c_pos, rfl⟩

private def detector : Fin 4 → Fin 4 := ![1, 0, 3, 2]

private theorem simple_raises (i : Fin 4) :
    Raises basisDegree ((F4Chevalley.rootCurve (sr i) (1 : CoefficientField 0)).val - 1) :=
  rootCurve_raises (sr i) (by rw [rootDegree_simple]; norm_num) 1

private theorem end_entry (i : Fin 4) (hi : i = 0 ∨ i = 3) :
    (endRootWord 0 1).val.val (.inr (sr i)) (.inl (node (detector i))) = 1 := by
  simp only [endRootWord, map_one, Subgroup.coe_mul, Units.val_mul, rootGeneratorInGroup_coe]
  rw [mul_entry (simple_raises 0) (simple_raises 3) _ _
    (simple_cartan_degree i (detector i)), simple_entry, simple_entry]
  rcases hi with rfl | rfl <;>
    norm_num [detector, typeF4CartanMatrix, Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem middle_entry (i : Fin 4) (hi : i = 1 ∨ i = 2) :
    middleWord.val.val (.inr (sr i)) (.inl (node (detector i))) = 1 := by
  have hc := rootCurve_raises c (by rw [rootDegree_c]; norm_num) (1 : CoefficientField 0)
  simp only [middleWord, Subgroup.coe_mul, Units.val_mul, rootGeneratorInGroup_coe]
  rw [mul_entry (raises_unit_mul (simple_raises 1) (simple_raises 2)) hc _ _
    (simple_cartan_degree i (detector i)),
    mul_entry (simple_raises 1) (simple_raises 2) _ _ (simple_cartan_degree i (detector i)),
    c_entry, simple_entry, simple_entry]
  rcases hi with rfl | rfl <;>
    norm_num [detector, typeF4CartanMatrix, Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Fixed positive root words detect all four simple roots on Cartan columns. -/
theorem simpleCoordinateWitnesses_of_blockRelations
    (hcomm : MixedRootCommutation 0) (hswap : B2RootSwap 0) :
    SimpleCoordinateWitnesses := by
  intro i
  by_cases hi : i = 0 ∨ i = 3
  · have hfixed : reeTwist 0 (endRootWord 0 1) = endRootWord 0 1 := by
      simpa only [LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply]
        using endRootWord_fixed (canonicalLocalBlockInput 0) (1 : CoefficientField 0)
    let x : Model 0 := ⟨endRootWord 0 1, (mem_fixedSubgroup 0 _).mpr hfixed⟩
    refine ⟨x, ?_, node (detector i), ?_⟩
    · change toSplitGroup 0 x ∈ splitUnipotent 0
      rw [toSplitGroup_apply]
      exact splitRadical_le_unipotent 0 .suzuki (endRootWord_mem_radical 0 1)
    · change (toSplitGroup 0 x).val.val _ _ ≠ 0
      rw [toSplitGroup_apply]
      change (endRootWord 0 1).val.val _ _ ≠ 0
      rw [end_entry i hi]
      exact one_ne_zero
  · have hi' : i = 1 ∨ i = 2 := by omega
    let x : Model 0 := ⟨middleWord, (mem_fixedSubgroup 0 _).mpr (middleWord_fixed hcomm hswap)⟩
    refine ⟨x, ?_, node (detector i), ?_⟩
    · change toSplitGroup 0 x ∈ splitUnipotent 0
      rw [toSplitGroup_apply]
      exact middleWord_mem
    · change (toSplitGroup 0 x).val.val _ _ ≠ 0
      rw [toSplitGroup_apply]
      change middleWord.val.val _ _ ≠ 0
      rw [middle_entry i hi']
      exact one_ne_zero

end ReeF4.Parabolics.Binary.FixedGeometry.WeylSeparation

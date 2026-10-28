module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.SquareDetection.MatrixLayer
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.SuzukiCoordinates

/-!
# Detecting torus characters by squares of middle Suzuki words

The positive middle B₂ word lies in the linear radical. Its square has
nonzero degree-two part whenever its first parameter is nonzero: the
mixed-root row and node-zero Cartan column give an explicit detecting entry.
Conjugation by the actual diagonal torus changes that parameter by its
second character. The first-layer calculation proves that an arbitrary
radical factor in the actor cannot remove this square.

Source: GLS3, Table 2.4(V), `refs/KGroup/GLS3/chapter2.tex`, and the linear
Ree local exclusion in Aschbacher–Smith 2.3.9(7), printed p.526, used in
E.6.8, pp.247–248 (`refs/quasithin.pdf`). The root subgroup and both torus
characters are those of the actual parabolic in F.1.12(I)(5), p.263.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open RootPairing.IntegralGeckConstruction
open ReeF4.SectionGeometry.LinearRadical.LeviDetection
namespace ReeF4.ConverseParabolics.CoreActionRigidity.SquareDetection
open LargeLocalSeeds
open LocalBlockInput.PairRigidity BlockParameters BlockParameters.FieldRecovery
open FullLeviRepresentation
open Parabolics.RadicalCoordinates.FixedCoordinates
variable {m : ℕ}

private theorem middle_root_radical (i : Fin 4) :
    IsRadicalRoot .linear (SuzukiChart.roots i) := by
  have he : ((rootBlocks (.radical .linear)).roots (.inr ((0 : Fin 4), i))).val =
      SuzukiChart.roots i := by
    rw [← SuzukiChart.roots_block]
    apply Subtype.ext
    rw [rootBlocks_roots_val, rootBlocks_roots_val]
    rfl
  exact he ▸ ((rootBlocks (.radical .linear)).roots
    (.inr ((0 : Fin 4), i))).property

private theorem middle_word_mem_radical (t u : CoefficientField m) :
    suzukiWord m true t u ∈ splitRadical m .linear := by
  have hr (i : Fin 4) (a : CoefficientField m) :
      rootGeneratorInGroup m (SuzukiChart.roots i) a ∈ splitRadical m .linear :=
    Subgroup.subset_closure ⟨_, _, middle_root_radical i, rfl⟩
  rw [SuzukiChart.word_eq, SuzukiChart.splitWord_def]
  exact mul_mem (mul_mem (mul_mem (hr 0 _) (hr 1 _)) (hr 2 _)) (hr 3 _)

/-- The actual positive middle Suzuki word in the Ree model. -/
def middleWord (t u : CoefficientField m) : Model m :=
  (canonicalLocalBlockInput m).modelEquiv
    ⟨suzukiWord m true t u, SuzukiChart.positive_fixed _ t u⟩

theorem middleWord_split (t u : CoefficientField m) :
    toSplitGroup m (middleWord t u) = suzukiWord m true t u := by
  rw [middleWord, toSplitGroup_apply, LocalBlockInput.modelEquiv_coe]

theorem middleWord_mem_radical (t u : CoefficientField m) :
    middleWord t u ∈ Parabolics.radical m .linear := by
  change toSplitGroup m (middleWord t u) ∈ splitRadical m .linear
  rw [middleWord_split]
  exact middle_word_mem_radical t u

theorem middleWord_mul (t u v w : CoefficientField m) :
    middleWord t u * middleWord v w =
      middleWord (t + v) (u + w + theta m t ^ 2 * v) := by
  apply toSplitGroup_injective m
  simp only [map_mul, middleWord_split, SuzukiChart.positive_mul]

theorem middleWord_zero : middleWord (0 : CoefficientField m) 0 = 1 := by
  apply toSplitGroup_injective m
  rw [middleWord_split, map_one, SuzukiChart.word_eq]
  have hp : SuzukiChart.parameters (0 : CoefficientField m) 0 = fun _ => 0 := by
    ext i
    fin_cases i <;> simp [SuzukiChart.parameters, Matrix.cons_val_two, Matrix.cons_val_three]
  rw [hp, SuzukiChart.splitWord_zero]

theorem middleWord_square (t u : CoefficientField m) :
    middleWord t u ^ 2 = middleWord 0 (theta m t ^ 2 * t) := by
  rw [pow_two, middleWord_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add]

theorem middleWord_inv_one : (middleWord (1 : CoefficientField m) 0)⁻¹ = middleWord 1 1 := by
  apply inv_eq_of_mul_eq_one_right
  rw [middleWord_mul]
  simpa only [map_one, one_pow, mul_one, zero_add, CharTwo.add_self_eq_zero] using middleWord_zero

private def matrixHom (m : ℕ) : Model m →* MatrixUnits m :=
  (SplitGroup m).subtype.comp (toSplitGroup m)

private theorem matrixHom_injective : Function.Injective (matrixHom m) :=
  Subtype.val_injective.comp (toSplitGroup_injective m)

private theorem matrixHom_torus (b c : (CoefficientField m)ˣ) :
    matrixHom m (torusElement b c) = (torusMatrix (blockTorus b c))⁻¹ :=
  torusElement_matrix b c

private theorem matrixHom_word (t u : CoefficientField m) :
    matrixHom m (middleWord t u) = (suzukiWord m true t u).val := by
  change (toSplitGroup m (middleWord t u)).val = _
  rw [middleWord_split]

theorem torus_conj_middleWord (b c : (CoefficientField m)ˣ) (t u : CoefficientField m) :
    torusElement b c * middleWord t u * (torusElement b c)⁻¹ =
      middleWord ((c : CoefficientField m) * t) ((centralScale c : CoefficientField m) * u) := by
  apply matrixHom_injective
  simp only [map_mul, map_inv, matrixHom_torus, matrixHom_word, inv_inv]
  exact blockTorus_suzukiWord b c true t u

open scoped commutatorElement

theorem middleWord_commutator_torus (b c : (CoefficientField m)ˣ) :
    ⁅middleWord (1 : CoefficientField m) 0, torusElement b c⁆ =
      middleWord (1 + (c : CoefficientField m)) ((centralScale c : CoefficientField m) + (c : CoefficientField m)) := by
  rw [commutatorElement_def, middleWord_inv_one]
  calc
    _ = middleWord 1 0 * (torusElement b c * middleWord 1 1 * (torusElement b c)⁻¹) := by group
    _ = _ := by
      rw [torus_conj_middleWord, mul_one, mul_one, middleWord_mul]
      simp only [map_one, one_pow, one_mul, zero_add]

private theorem middle_root_degree (i : Fin 4) :
    rootDegree (SuzukiChart.roots i) = ![1, 1, 2, 3] i := by
  have h := rootDegree_eq (SuzukiChart.roots i)
  rw [SuzukiChart.roots_val] at h
  fin_cases i <;>
    norm_num [typeF4SimpleCoefficient, Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢ <;>
    exact_mod_cast h

private theorem degreeTwoPart_dividedPower (r : F4Chevalley.Root) (n : ℕ) :
    degreeTwoPart (specializeMatrix (S := CoefficientField m)
      (F4Chevalley.integralOperators.rootDividedPower r n)) =
    if (n : ℤ) * rootDegree r = 2 then
      specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r n) else 0 := by
  by_cases h : (n : ℤ) * rootDegree r = 2
  · rw [if_pos h]
    ext i j
    by_cases hij : basisDegree i = basisDegree j + 2
    · simp [hij]
    · have hz : F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
        by_contra hne
        have hd := dividedPower_degree r n i j hne
        omega
      simp [hij, specializeMatrix, hz]
  · rw [if_neg h]
    ext i j
    by_cases hij : basisDegree i = basisDegree j + 2
    · have hz : F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
        by_contra hne
        have hd := dividedPower_degree r n i j hne
        omega
      simp [hij, specializeMatrix, hz]
    · simp [hij]

private theorem degreeTwoPart_middle_root (i : Fin 4) (hi : i = 2 ∨ i = 3)
    (t : CoefficientField m) :
    degreeTwoPart (rootGeneratorInGroup m (SuzukiChart.roots i) t).val.val =
      if i = 2 then t • rootOperator m (SuzukiChart.roots i) else 0 := by
  change degreeTwoPart (F4Chevalley.rootCurve _ t).val = _
  rw [F4Chevalley.rootCurve_matrix_formula]
  rcases hi with rfl | rfl <;>
    simp [map_add, degreeTwoPart_dividedPower, middle_root_degree, SectionGeometry.LinearRadical.LeviDetection.rootOperator,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem degreeTwoPart_middleWord_zero (u : CoefficientField m) :
    degreeTwoPart (modelMatrix m (middleWord 0 u)) =
      theta m u • rootOperator m (SuzukiChart.roots 2) := by
  have he : suzukiWord m true (0 : CoefficientField m) u =
      rootGeneratorInGroup m (SuzukiChart.roots 2) (theta m u) *
        rootGeneratorInGroup m (SuzukiChart.roots 3) u := by
    rw [SuzukiChart.word_eq, SuzukiChart.splitWord_def]
    simp only [SuzukiChart.parameters, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, map_zero, zero_mul, zero_add,
      SuzukiChart.X_zero, one_mul]
    rfl
  have hr (i : Fin 4) (a : CoefficientField m) :
      Raises ((rootGeneratorInGroup m (SuzukiChart.roots i) a).val.val - 1) :=
    splitRadical_raises _ (subset_closure ⟨_, _, middle_root_radical i, rfl⟩)
  rw [modelMatrix, middleWord_split, he]
  change degreeTwoPart (_ * _) = _
  rw [degreeTwoPart_mul_of_raises (hr 2 _) (hr 3 _),
    degreeTwoPart_middle_root 2 (Or.inl rfl), degreeTwoPart_middle_root 3 (Or.inr rfl),
    degreeOnePart_rootGenerator_of_one_lt _ (by rw [middle_root_degree]; decide),
    degreeOnePart_rootGenerator_of_one_lt _ (by rw [middle_root_degree]; decide)]
  simp

private theorem middle_operator_entry :
    rootOperator m (SuzukiChart.roots 2) (Sum.inr (SuzukiChart.roots 2))
      (Sum.inl (typeF4RootPairing_baseEquiv 0)) = 1 := by
  have h := congrFun
    (WordRelations.Faithfulness.Adjoint.PositiveSimple.coordinateOperator_mulVec_cartan m
      (SuzukiChart.roots 2) (typeF4RootPairing_baseEquiv 0)) (Sum.inr (SuzukiChart.roots 2))
  rw [Matrix.mulVec_single_one] at h
  have hp : typeF4RootPairing.pairingIn ℤ (SuzukiChart.roots 2)
      (typeF4SimpleRootIndex 0) = -1 := by
    have he : (typeF4RootPairing.pairingIn ℤ (SuzukiChart.roots 2)
        (typeF4SimpleRootIndex 0) : ℝ) = -1 := by
      change algebraMap ℤ ℝ _ = -1
      rw [typeF4RootPairing.algebraMap_pairingIn, typeF4RootPairing_pairing,
        typeF4CorootScale_simpleRoot, SuzukiChart.roots_val]
      norm_num [typeF4SimpleRoot, dot, Fin.sum_univ_four, basisVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
    exact_mod_cast he
  simpa [SectionGeometry.LinearRadical.LeviDetection.rootOperator, F4Chevalley.dividedPower_one, specializeMatrix,
    WordRelations.Faithfulness.Adjoint.coordinateOperator, Pi.single_apply,
    typeF4RootPairing_baseEquiv_val, hp, CharTwo.neg_eq] using h

theorem degreeTwoPart_middleWord_square_ne_zero (t u : CoefficientField m) (ht : t ≠ 0) :
    degreeTwoPart (modelMatrix m (middleWord t u ^ 2)) ≠ 0 := by
  rw [middleWord_square, degreeTwoPart_middleWord_zero]
  intro hz
  have he := congrArg (fun A : MatrixCarrier m => A (Sum.inr (SuzukiChart.roots 2))
    (Sum.inl (typeF4RootPairing_baseEquiv 0))) hz
  have hn : theta m (theta m t ^ 2 * t) ≠ 0 := by
    exact (map_ne_zero (theta m)).mpr
      (mul_ne_zero (pow_ne_zero 2 ((map_ne_zero (theta m)).mpr ht)) ht)
  apply hn
  simpa only [Matrix.smul_apply, smul_eq_mul, middle_operator_entry, mul_one, Matrix.zero_apply] using he


/-- An arbitrary radical factor cannot erase the square detected by a
nontrivial middle-root torus character. -/
theorem radical_torus_commutator_square_ne_one (r : Model m)
    (hr : r ∈ Parabolics.radical m .linear) (b c : (CoefficientField m)ˣ) (hc : c ≠ 1) :
    ⁅middleWord (1 : CoefficientField m) 0, r * torusElement b c⁆ ^ 2 ≠ 1 := by
  let q := middleWord (1 : CoefficientField m) 0
  let l := torusElement b c
  have hq : q ∈ Parabolics.radical m .linear := middleWord_mem_radical 1 0
  have hlq : l * q⁻¹ * l⁻¹ ∈ Parabolics.radical m .linear := by
    dsimp only [q, l]
    rw [middleWord_inv_one, torus_conj_middleWord]
    exact middleWord_mem_radical _ _
  have hy : ⁅q, l⁆ ∈ Parabolics.radical m .linear := by
    change ⁅middleWord 1 0, torusElement b c⁆ ∈ _
    rw [middleWord_commutator_torus]
    exact middleWord_mem_radical _ _
  have hx : ⁅q, r * l⁆ ∈ Parabolics.radical m .linear := by
    have he : ⁅q, r * l⁆ = q * (r * (l * q⁻¹ * l⁻¹) * r⁻¹) := by
      simp only [commutatorElement_def, mul_inv_rev]
      group
    rw [he]
    exact mul_mem hq (mul_mem (mul_mem hr hlq) (inv_mem hr))
  have he := degreeTwoPart_square_eq_of_degreeOnePart_eq hx hy
    (degreeOnePart_commutator_radical_mul q r l hq hr hlq)
  have ht : 1 + (c : CoefficientField m) ≠ 0 := by
    intro h
    apply hc
    apply Units.ext
    simpa only [CharTwo.neg_eq, Units.val_one] using eq_neg_of_add_eq_zero_right h
  have hn := degreeTwoPart_middleWord_square_ne_zero
    (1 + (c : CoefficientField m)) ((centralScale c : CoefficientField m) + (c : CoefficientField m)) ht
  rw [← middleWord_commutator_torus b c] at hn
  intro hz
  apply hn
  rw [← he, hz, modelMatrix_one, degreeTwoPart_one]

end ReeF4.ConverseParabolics.CoreActionRigidity.SquareDetection

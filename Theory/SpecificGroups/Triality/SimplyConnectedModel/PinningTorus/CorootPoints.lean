module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RootPoints

/-!
# Coroot point formulas in the Spin D4 model

The faithful natural action identifies each source coroot word with a
hyperbolic diagonal matrix. Thus the coroot point maps are multiplicative
and commute. These point identities fix the signs for a future regular
simple-coroot torus parametrization; they assert no regular inverse.

Source: GLS3, Theorem 1.12.1(c,d,g), with `h(t) = n(1)⁻¹ n(t)`.
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Pinning
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The natural-action diagonal of the source coroot word has exponent `-α`. -/
def corootDiagonal (r : RootIndex) (t : kˣ) (p : Fin 4) : kˣ :=
  if p = r.1.1.1 then (if r.2.1.1 = 1 then t⁻¹ else t)
  else if p = r.1.1.2 then (if r.2.2.1 = 1 then t⁻¹ else t)
  else 1

set_option linter.unusedSimpArgs false in
private theorem naturalAction_corootWord_negativeFirst
    (i j : Fin 4) (hij : i < j) (v : ({-1, 1} : Set ℝ)) (t : kˣ) :
    naturalAction k (corootWord k ⟨⟨⟨i, j⟩, hij⟩, ⟨-1, by simp⟩, v⟩ t) =
      hyperbolicDiagonalPoint 4 (corootDiagonal k ⟨⟨⟨i, j⟩, hij⟩, ⟨-1, by simp⟩, v⟩ t) := by
  classical
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have h3 : (3 : k) = 1 := by linear_combination h2
  have h4 : (4 : k) = 0 := by linear_combination 2 * h2
  have h6 : (6 : k) = 0 := by linear_combination 3 * h2
  rw [corootWord, normalizerWord_inv]
  simp only [normalizerWord, map_mul, naturalAction_rootPoint]
  rcases v with ⟨v, hv⟩
  rcases hv with hv | hv <;> subst v
  all_goals
    norm_num only [negativeRoot, evenOrthogonalRootQuadraticPoint,
      evenOrthogonalRootIsometry, reduceDIte]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    apply Prod.ext <;> funext p
  all_goals
    by_cases hpi : p = i
    · subst p
      simp [corootDiagonal, hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
        hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
        hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
        hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
        LinearEquiv.mul_apply, Pi.single_apply, hij.ne, hij.ne',
        CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul]
      norm_num [show (-1 : ℝ) ≠ 1 by norm_num]
      field_simp
      ring_nf
      simp [h2, h3, h4, h6]
    · by_cases hpj : p = j
      · subst p
        simp [corootDiagonal, hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
          hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
          hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
          hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
          LinearEquiv.mul_apply, Pi.single_apply, hij.ne, hij.ne',
          CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul]
        norm_num [show (-1 : ℝ) ≠ 1 by norm_num]
        field_simp
        ring_nf
        simp [h2, h3, h4, h6]
      · simp [corootDiagonal, hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
          hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
          hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
          hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
          LinearEquiv.mul_apply, Pi.single_apply, hij.ne, hij.ne', hpi, hpj]

set_option linter.unusedSimpArgs false in
private theorem naturalAction_corootWord_positiveFirst
    (i j : Fin 4) (hij : i < j) (v : ({-1, 1} : Set ℝ)) (t : kˣ) :
    naturalAction k (corootWord k ⟨⟨⟨i, j⟩, hij⟩, ⟨1, by simp⟩, v⟩ t) =
      hyperbolicDiagonalPoint 4 (corootDiagonal k ⟨⟨⟨i, j⟩, hij⟩, ⟨1, by simp⟩, v⟩ t) := by
  classical
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have h3 : (3 : k) = 1 := by linear_combination h2
  have h4 : (4 : k) = 0 := by linear_combination 2 * h2
  have h6 : (6 : k) = 0 := by linear_combination 3 * h2
  rw [corootWord, normalizerWord_inv]
  simp only [normalizerWord, map_mul, naturalAction_rootPoint]
  rcases v with ⟨v, hv⟩
  rcases hv with hv | hv <;> subst v
  all_goals
    norm_num only [negativeRoot, evenOrthogonalRootQuadraticPoint,
      evenOrthogonalRootIsometry, reduceDIte]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    apply Prod.ext <;> funext p
  all_goals
    by_cases hpi : p = i
    · subst p
      simp [corootDiagonal, hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
        hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
        hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
        hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
        LinearEquiv.mul_apply, Pi.single_apply, hij.ne, hij.ne',
        CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul]
      field_simp
      ring_nf
      simp [h2, h3, h4, h6]
    · by_cases hpj : p = j
      · subst p
        simp [corootDiagonal, hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
          hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
          hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
          hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
          LinearEquiv.mul_apply, Pi.single_apply, hij.ne, hij.ne',
          CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul]
        norm_num [show (-1 : ℝ) ≠ 1 by norm_num]
        field_simp
        ring_nf
        simp [h2, h3, h4, h6]
      · simp [corootDiagonal, hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
          hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
          hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
          hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
          LinearEquiv.mul_apply, Pi.single_apply, hij.ne, hij.ne', hpi, hpj]

/-- Direct matrix calculation for the source's ordered normalizer words. -/
theorem naturalAction_corootWord (r : RootIndex) (t : kˣ) :
    naturalAction k (corootWord k r t) =
      hyperbolicDiagonalPoint 4 (corootDiagonal k r t) := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, ⟨s, hs⟩, v⟩
  rcases hs with hs | hs <;> subst s
  · exact naturalAction_corootWord_negativeFirst k i j hij v t
  · exact naturalAction_corootWord_positiveFirst k i j hij v t

omit [IsAlgClosed k] [CharP k 2] in
/-- Multiplication of diagonal tuples is multiplication of their isometries. -/
private theorem diagonalPoint_mul (d e : Fin 4 → kˣ) :
    hyperbolicDiagonalPoint 4 (d * e) =
      hyperbolicDiagonalPoint 4 d * hyperbolicDiagonalPoint 4 e := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext i <;>
    simp [LinearEquiv.mul_apply, hyperbolicDiagonalPoint,
      hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv, mul_assoc, mul_comm]

omit [IsAlgClosed k] [CharP k 2] in
/-- The source coroot diagonals are multiplicative in their parameter. -/
theorem corootDiagonal_mul (r : RootIndex) (t u : kˣ) :
    corootDiagonal k r (t * u) = corootDiagonal k r t * corootDiagonal k r u := by
  classical
  funext p
  simp only [corootDiagonal, Pi.mul_apply]
  split_ifs <;> simp [mul_comm]

/-- Relation 1.12.1(d) on the actual Spin points. -/
theorem corootWord_mul (r : RootIndex) (t u : kˣ) :
    corootWord k r (t * u) = corootWord k r t * corootWord k r u := by
  apply naturalAction_injective k
  rw [map_mul, naturalAction_corootWord, naturalAction_corootWord,
    naturalAction_corootWord, corootDiagonal_mul, diagonalPoint_mul]

/-- Relation 1.12.1(c) on the actual Spin points. -/
theorem corootWord_commute (r s : RootIndex) (t u : kˣ) :
    Commute (corootWord k r t) (corootWord k s u) := by
  apply naturalAction_injective k
  simp only [map_mul, naturalAction_corootWord, ← diagonalPoint_mul]
  rw [mul_comm]

/-- Each source coroot word is a point-group homomorphism. -/
def corootPointHom (r : RootIndex) : kˣ →* Points k where
  toFun := corootWord k r
  map_one' := corootWord_one k r
  map_mul' := corootWord_mul k r

/-- Coroot conjugation agrees with the coordinate root scaling law. -/
theorem corootWord_rootPoint_conjugation (r s : RootIndex) (t : kˣ) (a : k) :
    (corootWord k s t)⁻¹ * rootPoint k r a * corootWord k s t =
      rootPoint k r (evenOrthogonalRootScale 4 r (corootDiagonal k s t) * a) := by
  apply rootPoint_conjugation_of_naturalAction
  rw [naturalAction_corootWord]
  exact evenOrthogonalRoot_diagonal_conjugation 4 r (corootDiagonal k s t) a

omit [IsAlgClosed k] [CharP k 2] in
/-- In the chosen D4 numbering, the simple-root/coroot exponents are the
entries of the standard Cartan matrix, with no sign change. -/
theorem simpleCoroot_rootScale (i j : Fin 4) (t : kˣ) :
    evenOrthogonalRootScale 4 (simpleRoot i) (corootDiagonal k (simpleRoot j) t) =
      (t : k) ^ typeDCartanMatrix 2 i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [evenOrthogonalRootScale, simpleRoot, typeDSimpleRootIndex,
      corootDiagonal, typeDCartanMatrix, pow_two, Fin.ext_iff, Fin.val_last]

/-- The numbered form of source relation 1.12.1(g). -/
theorem simpleCoroot_positiveSimplePoint_conjugation (i j : Fin 4) (t : kˣ) (a : k) :
    (simpleCoroot k j t)⁻¹ * positiveSimplePoint k i a * simpleCoroot k j t =
      positiveSimplePoint k i ((t : k) ^ typeDCartanMatrix 2 i j * a) := by
  simpa only [simpleCoroot_rootScale] using
    corootWord_rootPoint_conjugation k (simpleRoot i) (simpleRoot j) t a

end Triality.SimplyConnected.Pinning

module

public import Theory.SpecificGroups.ReeF4.DerivedTits.BruhatBound.Basic
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.RootPartition

/-!
# The sixteen binary Ree Weyl matrices and their positive root blocks

The faithful comparison with the F₄ Weyl group turns equality of the binary
matrix words into equality of their Euclidean root actions. An explicit
multiplication table proves that the sixteen alternating orbit words exhaust
the fixed Weyl subgroup. The same coordinate actions identify the commuting
pairs and B₂ quartets that remain positive at each representative.

These positive blocks supply the complementary parameters for the restricted
Bruhat-cell bounds. No group-order or presentation-realization premise enters
this calculation.

Sources: GLS3 §§2.3.2–2.3.5 and Table 2.4, `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace ReeF4.DerivedTits.BruhatBound
open Parabolics Parabolics.Binary.FixedGeometry LargeLocalSeeds
open Parabolics.Binary.FixedGeometry.BruhatCoverage.FixedWeyl
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction

private def simpleVector (i : Fin 4) (v : Vec 4) : Vec 4 :=
  ![![v 0, v 2, v 1, v 3],
    ![v 0, v 1, v 3, v 2],
    ![v 0, v 1, v 2, -v 3],
    ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]] i

private theorem simple_reflection_coordinates (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      simpleVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ _) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [simpleVector, typeF4SimpleRoot, dot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

private def wordVector : List (Fin 4) → Vec 4 → Vec 4
  | [], v => v
  | i :: l, v => simpleVector i (wordVector l v)

private theorem rootWord_coordinates (l : List (Fin 4)) (r : F4Chevalley.Root) :
    (typeF4RootPairing.weylGroupToPerm (rootWord l) r).val = wordVector l r.val := by
  rw [rootWord, ← reflectionWord_eq_weylGroupToPerm]
  induction l with
  | nil => rfl
  | cons i l ih =>
    simpa only [List.map_cons, reflectionWord, typeF4RootPairing_baseEquiv_val,
      simple_reflection_coordinates, wordVector] using congrArg (simpleVector i) ih

private theorem rootWord_eq_of_coordinates (l k : List (Fin 4))
    (h : ∀ v, wordVector l v = wordVector k v) : rootWord l = rootWord k := by
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective
  apply LinearEquiv.toLinearMap_injective
  apply typeF4RootPairing_base.toWeightBasis.ext
  intro i
  simp only [LinearEquiv.coe_coe, RootPairing.Base.toWeightBasis_apply]
  change rootWord l • typeF4RootPairing.root i = rootWord k • typeF4RootPairing.root i
  rw [typeF4RootPairing.weylGroup_apply_root, typeF4RootPairing.weylGroup_apply_root]
  change (typeF4RootPairing.weylGroupToPerm (rootWord l) i).val =
    (typeF4RootPairing.weylGroupToPerm (rootWord k) i).val
  rw [rootWord_coordinates, rootWord_coordinates, h]


/-- Euclidean actions of the sixteen actual relative Weyl words. -/
private def representativeVector : Fin 16 → Vec 4 → Vec 4
  | 0, v => ![v 0, v 1, v 2, v 3]
  | 1, v => ![(v 0 + v 1 + v 2 + v 3) / 2, (v 0 - v 1 + v 2 - v 3) / 2, (v 0 + v 1 - v 2 - v 3) / 2, (v 0 - v 1 - v 2 + v 3) / 2]
  | 2, v => ![v 0, v 1, - v 2, - v 3]
  | 3, v => ![(v 0 + v 1 - v 2 - v 3) / 2, (v 0 - v 1 - v 2 + v 3) / 2, (v 0 + v 1 + v 2 + v 3) / 2, (v 0 - v 1 + v 2 - v 3) / 2]
  | 4, v => ![(v 0 + v 1 + v 2 + v 3) / 2, (v 0 - v 1 + v 2 - v 3) / 2, (- v 0 - v 1 + v 2 + v 3) / 2, (- v 0 + v 1 + v 2 - v 3) / 2]
  | 5, v => ![v 2, v 3, v 0, v 1]
  | 6, v => ![(v 0 + v 1 - v 2 - v 3) / 2, (v 0 - v 1 - v 2 + v 3) / 2, (- v 0 - v 1 - v 2 - v 3) / 2, (- v 0 + v 1 - v 2 + v 3) / 2]
  | 7, v => ![- v 2, - v 3, v 0, v 1]
  | 8, v => ![v 2, v 3, - v 0, - v 1]
  | 9, v => ![(- v 0 - v 1 + v 2 + v 3) / 2, (- v 0 + v 1 + v 2 - v 3) / 2, (v 0 + v 1 + v 2 + v 3) / 2, (v 0 - v 1 + v 2 - v 3) / 2]
  | 10, v => ![- v 2, - v 3, - v 0, - v 1]
  | 11, v => ![(- v 0 - v 1 - v 2 - v 3) / 2, (- v 0 + v 1 - v 2 + v 3) / 2, (v 0 + v 1 - v 2 - v 3) / 2, (v 0 - v 1 - v 2 + v 3) / 2]
  | 12, v => ![(- v 0 - v 1 + v 2 + v 3) / 2, (- v 0 + v 1 + v 2 - v 3) / 2, (- v 0 - v 1 - v 2 - v 3) / 2, (- v 0 + v 1 - v 2 + v 3) / 2]
  | 13, v => ![- v 0, - v 1, v 2, v 3]
  | 14, v => ![(- v 0 - v 1 - v 2 - v 3) / 2, (- v 0 + v 1 - v 2 + v 3) / 2, (- v 0 - v 1 + v 2 + v 3) / 2, (- v 0 + v 1 + v 2 - v 3) / 2]
  | 15, v => ![- v 0, - v 1, - v 2, - v 3]
  | ⟨n + 16, h⟩, _ => False.elim (by omega)

private theorem wordVector_append (l k : List (Fin 4)) (v : Vec 4) :
    wordVector (l ++ k) v = wordVector l (wordVector k v) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, wordVector, ih]

/-- Right multiplication by the two orbit reflections in the finite list. -/
private def rightTransition : Side → Fin 16 → Fin 16
  | .linear => ![1, 0, 4, 5, 2, 3, 8, 9, 6, 7, 12, 13, 10, 11, 15, 14]
  | .suzuki => ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13]


private def sideIndex : Side → Fin 16
  | .linear => 1
  | .suzuki => 2

private theorem wordVector_side (s : Side) (v : Vec 4) :
    wordVector (sideWord s) v = representativeVector (sideIndex s) v := by
  cases s <;> ext j <;> fin_cases j <;>
    norm_num [sideIndex, sideWord, wordVector, simpleVector, representativeVector,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

private theorem vector_transition (i : Fin 16) (s : Side) (v : Vec 4) :
    representativeVector i (representativeVector (sideIndex s) v) =
      representativeVector (rightTransition s i) v := by
  cases s <;> fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [sideIndex, rightTransition, representativeVector,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem wordVector_representative (i : Fin 16) (v : Vec 4) :
    wordVector (splitWord i) v = representativeVector i v := by
  have h0 (v : Vec 4) : wordVector (splitWord 0) v = representativeVector 0 v := by
    ext j
    fin_cases j <;> rfl
  have h1 (v : Vec 4) : wordVector (splitWord 1) v = representativeVector 1 v := by
    change wordVector (splitWord 0 ++ sideWord .linear) v = _
    rw [wordVector_append, h0, wordVector_side]
    exact vector_transition 0 .linear v
  have h2 (v : Vec 4) : wordVector (splitWord 2) v = representativeVector 2 v := by
    change wordVector (splitWord 0 ++ sideWord .suzuki) v = _
    rw [wordVector_append, h0, wordVector_side]
    exact vector_transition 0 .suzuki v
  have h3 (v : Vec 4) : wordVector (splitWord 3) v = representativeVector 3 v := by
    change wordVector (splitWord 1 ++ sideWord .suzuki) v = _
    rw [wordVector_append, h1, wordVector_side]
    exact vector_transition 1 .suzuki v
  have h4 (v : Vec 4) : wordVector (splitWord 4) v = representativeVector 4 v := by
    change wordVector (splitWord 2 ++ sideWord .linear) v = _
    rw [wordVector_append, h2, wordVector_side]
    exact vector_transition 2 .linear v
  have h5 (v : Vec 4) : wordVector (splitWord 5) v = representativeVector 5 v := by
    change wordVector (splitWord 3 ++ sideWord .linear) v = _
    rw [wordVector_append, h3, wordVector_side]
    exact vector_transition 3 .linear v
  have h6 (v : Vec 4) : wordVector (splitWord 6) v = representativeVector 6 v := by
    change wordVector (splitWord 4 ++ sideWord .suzuki) v = _
    rw [wordVector_append, h4, wordVector_side]
    exact vector_transition 4 .suzuki v
  have h7 (v : Vec 4) : wordVector (splitWord 7) v = representativeVector 7 v := by
    change wordVector (splitWord 5 ++ sideWord .suzuki) v = _
    rw [wordVector_append, h5, wordVector_side]
    exact vector_transition 5 .suzuki v
  have h8 (v : Vec 4) : wordVector (splitWord 8) v = representativeVector 8 v := by
    change wordVector (splitWord 6 ++ sideWord .linear) v = _
    rw [wordVector_append, h6, wordVector_side]
    exact vector_transition 6 .linear v
  have h9 (v : Vec 4) : wordVector (splitWord 9) v = representativeVector 9 v := by
    change wordVector (splitWord 7 ++ sideWord .linear) v = _
    rw [wordVector_append, h7, wordVector_side]
    exact vector_transition 7 .linear v
  have h10 (v : Vec 4) : wordVector (splitWord 10) v = representativeVector 10 v := by
    change wordVector (splitWord 8 ++ sideWord .suzuki) v = _
    rw [wordVector_append, h8, wordVector_side]
    exact vector_transition 8 .suzuki v
  have h11 (v : Vec 4) : wordVector (splitWord 11) v = representativeVector 11 v := by
    change wordVector (splitWord 9 ++ sideWord .suzuki) v = _
    rw [wordVector_append, h9, wordVector_side]
    exact vector_transition 9 .suzuki v
  have h12 (v : Vec 4) : wordVector (splitWord 12) v = representativeVector 12 v := by
    change wordVector (splitWord 10 ++ sideWord .linear) v = _
    rw [wordVector_append, h10, wordVector_side]
    exact vector_transition 10 .linear v
  have h13 (v : Vec 4) : wordVector (splitWord 13) v = representativeVector 13 v := by
    change wordVector (splitWord 11 ++ sideWord .linear) v = _
    rw [wordVector_append, h11, wordVector_side]
    exact vector_transition 11 .linear v
  have h14 (v : Vec 4) : wordVector (splitWord 14) v = representativeVector 14 v := by
    change wordVector (splitWord 12 ++ sideWord .suzuki) v = _
    rw [wordVector_append, h12, wordVector_side]
    exact vector_transition 12 .suzuki v
  have h15 (v : Vec 4) : wordVector (splitWord 15) v = representativeVector 15 v := by
    change wordVector (splitWord 13 ++ sideWord .suzuki) v = _
    rw [wordVector_append, h13, wordVector_side]
    exact vector_transition 13 .suzuki v
  fin_cases i
  · exact h0 v
  · exact h1 v
  · exact h2 v
  · exact h3 v
  · exact h4 v
  · exact h5 v
  · exact h6 v
  · exact h7 v
  · exact h8 v
  · exact h9 v
  · exact h10 v
  · exact h11 v
  · exact h12 v
  · exact h13 v
  · exact h14 v
  · exact h15 v

/-- Coordinates of the genuine Weyl action, used below for root positivity. -/
private theorem representative_root_coordinates (i : Fin 16) (r : F4Chevalley.Root) :
    (typeF4RootPairing.weylGroupToPerm (rootWord (splitWord i)) r).val =
      representativeVector i r.val := by
  rw [rootWord_coordinates, wordVector_representative]

private theorem representative_mul_side (i : Fin 16) (s : Side) :
    weylRepresentative i * weylLift 0 s = weylRepresentative (rightTransition s i) := by
  apply toSplitGroup_injective 0
  rw [map_mul, toSplitGroup_weylRepresentative, toSplitGroup_weylLift,
    toSplitGroup_weylRepresentative, ← simpleWord_append]
  apply (simpleWord_eq_iff_rootWord_eq _ _).mpr
  apply rootWord_eq_of_coordinates
  intro v
  rw [wordVector_append, wordVector_representative, wordVector_representative]
  rw [wordVector_side]
  exact vector_transition i s v

private theorem weylLift_inv (s : Side) : (weylLift 0 s)⁻¹ = weylLift 0 s := by
  apply inv_eq_of_mul_eq_one_right
  have h := representative_mul_side (sideIndex s) s
  cases s <;> simpa [sideIndex, weylRepresentative, relativeWord, rightTransition] using h

/-- The sixteen concrete words exhaust the fixed Weyl matrix subgroup. -/
theorem weylRepresentative_cover :
    ∀ w ∈ weylSubgroup 0, ∃ i, weylRepresentative i = w := by
  intro w hw
  induction hw using Subgroup.closure_induction_right with
  | one => exact ⟨0, rfl⟩
  | mul_right x hx y hy ih =>
    obtain ⟨s, rfl⟩ := hy
    obtain ⟨i, rfl⟩ := ih
    exact ⟨rightTransition s i, (representative_mul_side i s).symm⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨s, rfl⟩ := hy
    obtain ⟨i, rfl⟩ := ih
    rw [weylLift_inv]
    exact ⟨rightTransition s i, (representative_mul_side i s).symm⟩


open RadicalCoordinates RadicalCoordinates.FixedCoordinates

private def degree (x : Vec 4) : ℝ := 8 * x 0 + 3 * x 1 + 2 * x 2 + x 3

private theorem positive_of_degree (r : F4Chevalley.Root) (h : 0 < degree r.val) :
    typeF4RootPairing_base.IsPos r := by
  classical
  by_contra hn
  let := typeF4RootPairing.indexNeg
  obtain ⟨i, hi⟩ := RootPartition.table_exhaustive (-r)
    ((RootPairing.Base.IsPos.neg_iff_not _ r).mpr hn)
  have hd : 0 < degree (RootPartition.table i) := by
    fin_cases i <;> norm_num [degree, RootPartition.table,
      Matrix.cons_val_two, Matrix.cons_val_three]
  have hv : (-r).val = -r.val := by
    change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  have he := congrArg degree hi
  rw [hv] at he
  simp only [degree, Pi.neg_apply] at he hd h
  linarith

/-- Blocks whose roots remain positive under the representative. -/
def positivePairs : Fin 16 → Finset (Fin 4) :=
  ![{0, 1, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}, {0, 2, 3}, {1, 2, 3}, {1, 3}, {0, 2, 3}, {0, 2}, {1, 3}, {1}, {0, 2}, {0}, {1}, ∅, {0}, ∅]

/-- Blocks whose roots remain positive under the representative. -/
def positiveQuartets : Fin 16 → Finset (Fin 4) :=
  ![{0, 1, 2, 3}, {0, 1, 2, 3}, {1, 2, 3}, {1, 2, 3}, {0, 1, 3}, {0, 1, 3}, {1, 2}, {1, 2}, {0, 3}, {0, 3}, {2}, {2}, {0}, {0}, ∅, ∅]

/-- Positivity is checked in the actual Euclidean F₄ root action. -/
theorem positive_pairs_root (i : Fin 16) (j : Fin 4) (hj : j ∈ positivePairs i) (k : Fin 2) :
    typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm (rootWord (splitWord i))
      ((rootBlocks .positive).roots (.inl (j, k))).val) := by
  apply positive_of_degree
  rw [representative_root_coordinates, rootBlocks_roots_val]
  fin_cases i <;> fin_cases j <;> simp [positivePairs] at hj <;> fin_cases k <;>
    norm_num [representativeVector, degree, RootPartition.index, RootPartition.pairRow,
      RootPartition.quartetRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Positivity is checked in the actual Euclidean F₄ root action. -/
theorem positive_quartets_root (i : Fin 16) (j : Fin 4) (hj : j ∈ positiveQuartets i) (k : Fin 4) :
    typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm (rootWord (splitWord i))
      ((rootBlocks .positive).roots (.inr (j, k))).val) := by
  apply positive_of_degree
  rw [representative_root_coordinates, rootBlocks_roots_val]
  fin_cases i <;> fin_cases j <;> simp [positiveQuartets] at hj <;> fin_cases k <;>
    norm_num [representativeVector, degree, RootPartition.index, RootPartition.pairRow,
      RootPartition.quartetRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Number of free fixed coordinates provided by the positive blocks. -/
theorem positive_block_exponents (i : Fin 16) :
    (positivePairs i).card + 2 * (positiveQuartets i).card + cellExponent i = 12 := by
  fin_cases i <;> decide

end ReeF4.DerivedTits.BruhatBound

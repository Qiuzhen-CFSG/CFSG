module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order.Bruhat
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.RootPartition

/-!
# Relative Weyl representatives and their inversion blocks

The sixteen alternating relative words act on the actual Euclidean F₄ roots.
The multiplication table proves coverage, and their actions distinguish the
representatives. Positive and negative blocks are computed in this root action.
The general-field Tits-word comparison transfers the table to every Ree field.

This extends the binary geometry in `DerivedTits/BruhatBound/Geometry.lean`.
Source: GLS3 2.3.2–2.3.8 and Table 2.4, `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.CentralCovers.OddPrimary.Order.CellCardinalities
open Parabolics Parabolics.Binary.FixedGeometry LargeLocalSeeds
open Parabolics.Binary.FixedGeometry.BruhatCoverage.FixedWeyl
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction

/-- Alternating words of relative lengths zero through eight, with the
linear-starting word first at each of lengths one through seven. -/
def relativeWord : Fin 16 → List Side :=
  ![[], [.linear], [.suzuki], [.linear, .suzuki], [.suzuki, .linear],
    [.linear, .suzuki, .linear], [.suzuki, .linear, .suzuki],
    [.linear, .suzuki, .linear, .suzuki], [.suzuki, .linear, .suzuki, .linear],
    [.linear, .suzuki, .linear, .suzuki, .linear],
    [.suzuki, .linear, .suzuki, .linear, .suzuki],
    [.linear, .suzuki, .linear, .suzuki, .linear, .suzuki],
    [.suzuki, .linear, .suzuki, .linear, .suzuki, .linear],
    [.linear, .suzuki, .linear, .suzuki, .linear, .suzuki, .linear],
    [.suzuki, .linear, .suzuki, .linear, .suzuki, .linear, .suzuki],
    [.linear, .suzuki, .linear, .suzuki, .linear, .suzuki, .linear, .suzuki]]

/-- The corresponding words in the four numbered split simple reflections. -/
def splitWord (i : Fin 16) : List (Fin 4) :=
  ((relativeWord i).map sideWord).flatten

/-- Actual fixed matrices represented by the sixteen alternating words. -/
def weylRepresentative (m : ℕ) (i : Fin 16) : Model m :=
  ((relativeWord i).map (weylLift m)).prod

theorem weylRepresentative_mem (m : ℕ) (i : Fin 16) :
    weylRepresentative m i ∈ weylSubgroup m := by
  apply Subgroup.list_prod_mem
  intro n hn
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hn
  exact weylLift_mem_weylSubgroup m s

/-- The fixed representative has exactly the stated split matrix word. -/
theorem toSplitGroup_weylRepresentative (m : ℕ) (i : Fin 16) :
    toSplitGroup m (weylRepresentative m i) = simpleWord m (splitWord i) := by
  have h (l : List Side) :
      toSplitGroup m ((l.map (weylLift m)).prod) =
        simpleWord m ((l.map sideWord).flatten) := by
    induction l with
    | nil => simp [simpleWord]
    | cons s l ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, toSplitGroup_weylLift,
        List.flatten_cons, simpleWord_append, ih]
  exact h (relativeWord i)

/-- Inversion exponents in the order `relativeWord`.
Pairs contribute one field parameter and B₂ quartets contribute two. -/
def cellExponent : Fin 16 → ℕ :=
  ![0, 1, 2, 3, 3, 4, 5, 6, 6, 7, 8, 9, 9, 10, 11, 12]

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

private theorem representative_mul_side (m : ℕ) (i : Fin 16) (s : Side) :
    weylRepresentative m i * weylLift m s = weylRepresentative m (rightTransition s i) := by
  apply toSplitGroup_injective m
  rw [map_mul, toSplitGroup_weylRepresentative, toSplitGroup_weylLift,
    toSplitGroup_weylRepresentative, ← simpleWord_append]
  apply (SectionGeometry.BNPair.QuotientGeometry.simpleWord_eq_iff m _ _).mpr
  apply rootWord_eq_of_coordinates
  intro v
  rw [wordVector_append, wordVector_representative, wordVector_representative]
  rw [wordVector_side]
  exact vector_transition i s v

private theorem weylLift_inv (m : ℕ) (s : Side) : (weylLift m s)⁻¹ = weylLift m s := by
  apply inv_eq_of_mul_eq_one_right
  have h := representative_mul_side m (sideIndex s) s
  cases s <;> simpa [sideIndex, weylRepresentative, relativeWord, rightTransition] using h

/-- The sixteen concrete words exhaust the fixed Weyl matrix subgroup. -/
theorem weylRepresentative_cover (m : ℕ) :
    ∀ w ∈ weylSubgroup m, ∃ i, weylRepresentative m i = w := by
  intro w hw
  induction hw using Subgroup.closure_induction_right with
  | one => exact ⟨0, rfl⟩
  | mul_right x hx y hy ih =>
    obtain ⟨s, rfl⟩ := hy
    obtain ⟨i, rfl⟩ := ih
    exact ⟨rightTransition s i, (representative_mul_side m i s).symm⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨s, rfl⟩ := hy
    obtain ⟨i, rfl⟩ := ih
    rw [weylLift_inv m]
    exact ⟨rightTransition s i, (representative_mul_side m i s).symm⟩


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


private theorem not_positive_of_degree (r : F4Chevalley.Root) (h : degree r.val < 0) :
    ¬ typeF4RootPairing_base.IsPos r := by
  intro hp
  obtain ⟨i, hi⟩ := RootPartition.table_exhaustive r hp
  have hd : 0 < degree (RootPartition.table i) := by
    fin_cases i <;> norm_num [degree, RootPartition.table,
      Matrix.cons_val_two, Matrix.cons_val_three]
  rw [← hi] at h
  linarith

/-- Every root in an unselected pair is inverted by the actual representative. -/
theorem negative_pairs_root (i : Fin 16) (j : Fin 4) (hj : j ∉ positivePairs i) (k : Fin 2) :
    ¬ typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm (rootWord (splitWord i))
      ((rootBlocks .positive).roots (.inl (j, k))).val) := by
  apply not_positive_of_degree
  rw [representative_root_coordinates, rootBlocks_roots_val]
  fin_cases i <;> fin_cases j <;> simp [positivePairs] at hj <;> fin_cases k <;>
    norm_num [representativeVector, degree, RootPartition.index, RootPartition.pairRow,
      RootPartition.quartetRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Every root in an unselected quartet is inverted by the actual representative. -/
theorem negative_quartets_root (i : Fin 16) (j : Fin 4)
    (hj : j ∉ positiveQuartets i) (k : Fin 4) :
    ¬ typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm (rootWord (splitWord i))
      ((rootBlocks .positive).roots (.inr (j, k))).val) := by
  apply not_positive_of_degree
  rw [representative_root_coordinates, rootBlocks_roots_val]
  fin_cases i <;> fin_cases j <;> simp [positiveQuartets] at hj <;> fin_cases k <;>
    norm_num [representativeVector, degree, RootPartition.index, RootPartition.pairRow,
      RootPartition.quartetRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]

/-- The inverted commuting pairs contribute one parameter and quartets two. -/
theorem negative_block_exponents (i : Fin 16) :
    (positivePairs i)ᶜ.card + 2 * (positiveQuartets i)ᶜ.card = cellExponent i := by
  fin_cases i <;> decide

private theorem blockSigns_injective :
    Function.Injective (fun i => (positivePairs i, positiveQuartets i)) := by decide

/-- The root action distinguishes all sixteen alternating words. -/
theorem weylRepresentative_injective (m : ℕ) : Function.Injective (weylRepresentative m) := by
  intro i j he
  have hs := congrArg (toSplitGroup m) he
  rw [toSplitGroup_weylRepresentative, toSplitGroup_weylRepresentative] at hs
  have hr := (SectionGeometry.BNPair.QuotientGeometry.simpleWord_eq_iff m _ _).mp hs
  apply blockSigns_injective
  apply Prod.ext
  · ext k
    constructor
    · intro hi
      by_contra hj
      have hp := positive_pairs_root i k hi 0
      rw [hr] at hp
      exact negative_pairs_root j k hj 0 hp
    · intro hj
      by_contra hi
      have hp := positive_pairs_root j k hj 0
      rw [← hr] at hp
      exact negative_pairs_root i k hi 0 hp
  · ext k
    constructor
    · intro hi
      by_contra hj
      have hp := positive_quartets_root i k hi 0
      rw [hr] at hp
      exact negative_quartets_root j k hj 0 hp
    · intro hj
      by_contra hi
      have hp := positive_quartets_root j k hj 0
      rw [← hr] at hp
      exact negative_quartets_root i k hi 0 hp

/-- The actual relative Weyl matrix subgroup has these sixteen elements, without repetitions. -/
def weylEquiv (m : ℕ) : Fin 16 ≃ weylSubgroup m :=
  Equiv.ofBijective (fun i => ⟨weylRepresentative m i, weylRepresentative_mem m i⟩)
    ⟨fun _ _ h => weylRepresentative_injective m (congrArg Subtype.val h), by
      intro w
      obtain ⟨i, hi⟩ := weylRepresentative_cover m w.val w.property
      exact ⟨i, Subtype.ext hi⟩⟩

end ReeF4.CentralCovers.OddPrimary.Order.CellCardinalities

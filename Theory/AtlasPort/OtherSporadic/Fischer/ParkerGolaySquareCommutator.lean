/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Fischer/ParkerGolaySquareCommutator.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Fischer.ParkerGolayIdentities
public import Theory.AtlasPort.OtherSporadic.Fischer.GolayPolarization

/-!
# Squares and commutators of the Golay factor set

Binary basis determination extends the weight and overlap formulas from
basis pairs to every pair of Golay words.

Source: Gerald Höhn, ATLAS, `Atlas/Fischer/ParkerGolaySquareCommutator.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Coordinate definitions are exposed for downstream reductions.
-/

@[expose] public section

namespace Atlas.Fischer
open Atlas.Codes

theorem parkerTripleIntersection_cycle (a b c : BinaryWord) :
    parkerTripleIntersection a b c = parkerTripleIntersection c a b := by
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem bit_twice (x : ParkerBit) : x + x = 0 := by
  have h : ∀ x : ParkerBit, x + x = 0 := by decide
  exact h x

theorem parkerGolayFactorSet_basis_commutator (i j : Fin 12) :
    parkerGolayFactorSet (golayBasis i) (golayBasis j) +
      parkerGolayFactorSet (golayBasis j) (golayBasis i) =
        golayHalfOverlap (golayBasis i) (golayBasis j) := by
  rw [parkerGolayFactorSet_basis, parkerGolayFactorSet_basis]
  rcases lt_trichotomy i j with h | h | h
  · simp [parkerGolayBilinearCoefficients, ne_of_lt h, ne_of_gt h,
      h, not_lt_of_gt h, golayHalfOverlap]
  · subst j
    rw [bit_twice]
    unfold golayHalfOverlap overlap
    simp only [and_self]
    change 0 = ((hammingNorm (golayBasis i : BinaryWord) / 2 : ℕ) : Bit)
    rw [golay_octad_basis.2 i]
    rfl
  · rw [golayHalfOverlap_symmetric]
    simp [parkerGolayBilinearCoefficients, ne_of_lt h, ne_of_gt h,
      h, not_lt_of_gt h, golayHalfOverlap]

theorem parkerGolayFactorSet_commutator (a b : golay) :
    parkerGolayFactorSet a b + parkerGolayFactorSet b a = golayHalfOverlap a b := by
  let d : golay → golay → ParkerBit := fun x y =>
    parkerGolayFactorSet x y + parkerGolayFactorSet y x + golayHalfOverlap x y
  have hs : ∀ x y, d x y = d y x := by
    intro x y
    dsimp [d]
    rw [golayHalfOverlap_symmetric x y]
    ring
  have hz : ∀ y, d 0 y = 0 := by intro y; simp [d]
  have ha : ∀ x x' y, d (x + x') y = d x y + d x' y := by
    intro x x' y
    dsimp [d]
    rw [parkerGolayFactorSet_add_left, parkerGolayFactorSet_add_right,
      golayHalfOverlap_add_left, parkerTripleIntersection_cycle x.val x'.val y.val]
    ring_nf
    simp only [show (2 : ParkerBit) = 0 from rfl, mul_zero, add_zero]
  have hr : ∀ x y y', d x (y + y') = d x y + d x y' := by
    intro x y y'
    rw [hs x (y + y'), ha, hs y x, hs y' x]
  have hb : ∀ i j, d (golayBasis i) (golayBasis j) = 0 := by
    intro i j
    dsimp [d]
    rw [parkerGolayFactorSet_basis_commutator, bit_twice]
  have hd := parkerBinary_biadditive_eq_zero_of_basis golayBasis d hz
    (fun x => by rw [hs, hz]) ha hr hb a b
  have h := congrArg (fun x => x + golayHalfOverlap a b) hd
  simpa only [d, add_assoc, bit_twice, add_zero, zero_add] using h

theorem parkerGolayFactorSet_square (a : golay) :
    parkerGolayFactorSet a a = golayQuarterWeight a := by
  let d : golay → ParkerBit := fun x => parkerGolayFactorSet x x + golayQuarterWeight x
  have hz : d 0 = 0 := by simp [d]
  have ha : ∀ x y, d (x + y) = d x + d y := by
    intro x y
    dsimp [d]
    rw [parkerGolayFactorSet_add_left, parkerGolayFactorSet_add_right,
      parkerGolayFactorSet_add_right, golayQuarterWeight_add]
    rw [parkerTripleIntersection_cycle x.val x.val y.val,
      parkerTripleIntersection_repeat, parkerTripleIntersection_cycle y.val x.val y.val,
      parkerTripleIntersection_cycle y.val y.val x.val,
      parkerTripleIntersection_repeat, ← parkerGolayFactorSet_commutator x y]
    ring_nf
    simp only [show (2 : ParkerBit) = 0 from rfl, mul_zero, add_zero]
  have hb : ∀ i, d (golayBasis i) = 0 := by
    intro i
    dsimp [d]
    rw [parkerGolayFactorSet_basis]
    simp only [parkerGolayBilinearCoefficients, ite_true, golayQuarterWeight]
    exact bit_twice _
  have hd := parkerBinary_eq_zero_of_basis golayBasis d hz ha hb a
  have h := congrArg (fun x => x + golayQuarterWeight a) hd
  simpa only [d, add_assoc, bit_twice, add_zero, zero_add] using h

end Atlas.Fischer

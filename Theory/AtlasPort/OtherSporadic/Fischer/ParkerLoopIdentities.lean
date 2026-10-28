/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Fischer/ParkerLoopIdentities.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Fischer.ParkerGolaySquareCommutator
public import Theory.AtlasPort.OtherSporadic.Fischer.Cocode

/-!
# Identities in the concrete Parker loop

The factor-set identities give the loop squares, commutators and
associators. The all-ones Golay word defines a central involution.

Source: Gerald Höhn, ATLAS, `Atlas/Fischer/ParkerLoopIdentities.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Coordinate definitions are exposed for downstream reductions.
-/

@[expose] public section

namespace Atlas.Fischer
open Atlas.Codes

def parkerSign (s : ParkerBit) (x : ParkerLoop) : ParkerLoop := (x.1, x.2 + s)

def parkerOmega : ParkerLoop := (golayOne, 0)

@[simp] theorem parkerSign_zero (x : ParkerLoop) : parkerSign 0 x = x := by
  simp [parkerSign]

theorem parkerSign_add (s t : ParkerBit) (x : ParkerLoop) :
    parkerSign s (parkerSign t x) = parkerSign (s + t) x := by
  apply Prod.ext
  · rfl
  · change (x.2 + t) + s = x.2 + (s + t)
    ring

theorem parkerLoopMultiply_sign_left (s : ParkerBit) (x y : ParkerLoop) :
    parkerLoopMultiply (parkerSign s x) y = parkerSign s (parkerLoopMultiply x y) := by
  apply Prod.ext
  · rfl
  · change (x.2 + s) + y.2 + parkerGolayFactorSet x.1 y.1 =
      (x.2 + y.2 + parkerGolayFactorSet x.1 y.1) + s
    ring

theorem parkerLoopMultiply_sign_right (s : ParkerBit) (x y : ParkerLoop) :
    parkerLoopMultiply x (parkerSign s y) = parkerSign s (parkerLoopMultiply x y) := by
  apply Prod.ext
  · rfl
  · change x.2 + (y.2 + s) + parkerGolayFactorSet x.1 y.1 =
      (x.2 + y.2 + parkerGolayFactorSet x.1 y.1) + s
    ring

theorem parkerGolay_add_self (a : golay) : a + a = 0 := by
  apply Subtype.ext
  funext p
  change (a : BinaryWord) p + (a : BinaryWord) p = 0
  have h : ∀ x : Bit, x + x = 0 := by decide
  exact h _

theorem parkerLoopMultiply_square (x : ParkerLoop) :
    parkerLoopMultiply x x = (0, golayQuarterWeight x.1) := by
  rw [parkerLoopMultiply, parkerMultiply_square, parkerGolay_add_self,
    parkerGolayFactorSet_square]

theorem parkerLoopMultiply_commutator (x y : ParkerLoop) :
    parkerLoopMultiply x y = parkerSign (golayHalfOverlap x.1 y.1)
      (parkerLoopMultiply y x) := by
  apply Prod.ext
  · exact add_comm _ _
  · change x.2 + y.2 + parkerGolayFactorSet x.1 y.1 =
      y.2 + x.2 + parkerGolayFactorSet y.1 x.1 + golayHalfOverlap x.1 y.1
    rw [← parkerGolayFactorSet_commutator]
    ring_nf
    simp only [show (2 : ParkerBit) = 0 from rfl, mul_zero, add_zero]

theorem parkerLoopMultiply_associator (x y z : ParkerLoop) :
    parkerLoopMultiply (parkerLoopMultiply x y) z =
      parkerSign (parkerTripleIntersection x.1 y.1 z.1)
        (parkerLoopMultiply x (parkerLoopMultiply y z)) := by
  apply Prod.ext
  · exact add_assoc _ _ _
  · change x.2 + y.2 + parkerGolayFactorSet x.1 y.1 + z.2 +
        parkerGolayFactorSet (x.1 + y.1) z.1 =
      x.2 + (y.2 + z.2 + parkerGolayFactorSet y.1 z.1) +
        parkerGolayFactorSet x.1 (y.1 + z.1) + parkerTripleIntersection x.1 y.1 z.1
    rw [← parkerGolayFactorSet_associator]
    ring_nf
    simp only [show (2 : ParkerBit) = 0 from rfl, mul_zero, add_zero]

theorem parkerOmega_square : parkerLoopMultiply parkerOmega parkerOmega = (0, 0) := by
  rw [parkerLoopMultiply_square]
  apply Prod.ext rfl
  change golayQuarterWeight golayOne = 0
  unfold golayQuarterWeight
  rw [(weight_twentyfour_iff golayOne.val).mpr rfl]
  rfl

theorem golayHalfOverlap_one (a : golay) : golayHalfOverlap golayOne a = 0 := by
  have ho : overlap allOnes a.val = hammingNorm a.val := by
    simp [overlap, allOnes, hammingNorm]
  have hd := golay_doublyEven a.val a.property
  have hh : hammingNorm a.val / 2 = 2 * (hammingNorm a.val / 4) := by omega
  change ((overlap allOnes a.val / 2 : ℕ) : Bit) = 0
  rw [ho, hh, Nat.cast_mul]
  change (2 : Bit) * ((hammingNorm a.val / 4 : ℕ) : Bit) = 0
  simp only [show (2 : Bit) = 0 from rfl, zero_mul]

theorem parkerOmega_commutes (x : ParkerLoop) :
    parkerLoopMultiply parkerOmega x = parkerLoopMultiply x parkerOmega := by
  rw [parkerLoopMultiply_commutator]
  change parkerSign (golayHalfOverlap golayOne x.1) _ = _
  rw [golayHalfOverlap_one, parkerSign_zero]

theorem parkerTripleIntersection_one (a b : golay) :
    parkerTripleIntersection golayOne a b = 0 := by
  have h := golay_selfOrthogonal b.property a.val a.property
  simpa only [parkerTripleIntersection, golayOne, allOnes, one_mul,
    binaryDot_apply] using h

theorem parkerOmega_associates_left (x y : ParkerLoop) :
    parkerLoopMultiply (parkerLoopMultiply parkerOmega x) y =
      parkerLoopMultiply parkerOmega (parkerLoopMultiply x y) := by
  rw [parkerLoopMultiply_associator]
  change parkerSign (parkerTripleIntersection golayOne x.1 y.1) _ = _
  rw [parkerTripleIntersection_one, parkerSign_zero]

theorem parkerOmega_associates_middle (x y : ParkerLoop) :
    parkerLoopMultiply (parkerLoopMultiply x parkerOmega) y =
      parkerLoopMultiply x (parkerLoopMultiply parkerOmega y) := by
  rw [parkerLoopMultiply_associator]
  change parkerSign (parkerTripleIntersection x.1 golayOne y.1) _ = _
  rw [parkerTripleIntersection_cycle, parkerTripleIntersection_cycle _ _ golayOne.val,
    parkerTripleIntersection_one, parkerSign_zero]

theorem parkerOmega_associates_right (x y : ParkerLoop) :
    parkerLoopMultiply (parkerLoopMultiply x y) parkerOmega =
      parkerLoopMultiply x (parkerLoopMultiply y parkerOmega) := by
  rw [parkerLoopMultiply_associator]
  change parkerSign (parkerTripleIntersection x.1 y.1 golayOne) _ = _
  rw [parkerTripleIntersection_cycle, parkerTripleIntersection_one, parkerSign_zero]

end Atlas.Fischer

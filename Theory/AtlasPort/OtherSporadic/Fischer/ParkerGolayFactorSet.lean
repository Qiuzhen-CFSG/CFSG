/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Fischer/ParkerGolayFactorSet.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Fischer.ParkerOrderedFactorSet
public import Theory.AtlasPort.OtherSporadic.Codes.GolayBasis

/-!
# The concrete Golay factor set and Parker loop

The ordered octad basis gives explicit coefficients for the factor set on
the actual Golay code. Basis expansion proves its triple-intersection defect.

Source: Gerald Höhn, ATLAS, `Atlas/Fischer/ParkerGolayFactorSet.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Coordinate definitions are exposed for downstream reductions.
-/

@[expose] public section

namespace Atlas.Fischer

open scoped BigOperators
open Atlas.Codes

/-- Triple intersection parity on the retained marked binary coordinates. -/
def parkerTripleIntersection (a b c : BinaryWord) : ParkerBit :=
  ∑ i, a i * b i * c i

noncomputable def parkerGolayTripleCoefficients (i j k : Fin 12) : ParkerBit :=
  parkerTripleIntersection (golayBasis i) (golayBasis j) (golayBasis k)

/-- The diagonal and upper triangular coefficients of the manuscript. -/
noncomputable def parkerGolayBilinearCoefficients (i j : Fin 12) : ParkerBit :=
  if i = j then (hammingNorm (golayBasis i : BinaryWord) / 4 : ℕ)
  else if i < j then (overlap (golayBasis i : BinaryWord) (golayBasis j : BinaryWord) / 2 : ℕ)
  else 0

noncomputable def parkerGolayFactorSet (a b : golay) : ParkerBit :=
  parkerOrderedFactorSet parkerGolayTripleCoefficients parkerGolayBilinearCoefficients
    (golayBasis.repr a) (golayBasis.repr b)

/-- The actual retained Golay code with additive sign coordinates. -/
abbrev ParkerLoop := golay × ParkerBit

noncomputable def parkerLoopMultiply : ParkerLoop → ParkerLoop → ParkerLoop :=
  parkerMultiply parkerGolayFactorSet

@[simp] theorem parkerGolayFactorSet_zero_left (a : golay) :
    parkerGolayFactorSet 0 a = 0 := by
  simp [parkerGolayFactorSet, parkerOrderedFactorSet, parkerOrderedTheta, parkerOrderedBeta]

@[simp] theorem parkerGolayFactorSet_zero_right (a : golay) :
    parkerGolayFactorSet a 0 = 0 := by
  simp [parkerGolayFactorSet, parkerOrderedFactorSet, parkerOrderedTheta, parkerOrderedBeta]

theorem parkerLoopMultiply_one_left (x : ParkerLoop) :
    parkerLoopMultiply (0, 0) x = x :=
  parkerMultiply_one_left _ parkerGolayFactorSet_zero_left x

theorem parkerLoopMultiply_one_right (x : ParkerLoop) :
    parkerLoopMultiply x (0, 0) = x :=
  parkerMultiply_one_right _ parkerGolayFactorSet_zero_right x

theorem parkerGolayFactorSet_defect (a b c : golay) :
    parkerGolayFactorSet a b + parkerGolayFactorSet (a + b) c +
      parkerGolayFactorSet b c + parkerGolayFactorSet a (b + c) =
    parkerOrderedTheta parkerGolayTripleCoefficients
        (golayBasis.repr a) (golayBasis.repr b) (golayBasis.repr c) +
      parkerOrderedTheta parkerGolayTripleCoefficients
        (golayBasis.repr a) (golayBasis.repr c) (golayBasis.repr b) := by
  simpa only [parkerGolayFactorSet, map_add, Finsupp.coe_add] using
    parkerOrderedFactorSet_defect parkerGolayTripleCoefficients parkerGolayBilinearCoefficients
      (golayBasis.repr a) (golayBasis.repr b) (golayBasis.repr c)

theorem parkerTripleIntersection_swap (a b c : BinaryWord) :
    parkerTripleIntersection a b c = parkerTripleIntersection a c b := by
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem parkerTripleIntersection_repeat (a b : golay) :
    parkerTripleIntersection a b b = 0 := by
  have hbit : ∀ x : Bit, x * x = x := by decide
  have he : parkerTripleIntersection a b b = binaryDot (a : BinaryWord) (b : BinaryWord) := by
    simp only [parkerTripleIntersection, binaryDot_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc, hbit]
  rw [he]
  exact golay_selfOrthogonal b.property a.val a.property

theorem parkerGolay_coordinate_expand (a : golay) (p : Omega) :
    (a : BinaryWord) p = ∑ i, golayBasis.repr a i * (golayBasis i : BinaryWord) p := by
  have h := congrArg (fun z : golay => (z : BinaryWord) p) (golayBasis.sum_repr a)
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul] using h.symm

theorem parkerTripleIntersection_basis_expand (a b c : golay) :
    parkerTripleIntersection a b c =
      ∑ i, ∑ j, ∑ k, golayBasis.repr a i * golayBasis.repr b j * golayBasis.repr c k *
        parkerGolayTripleCoefficients i j k := by
  have ha := parkerGolay_coordinate_expand a
  have hb := parkerGolay_coordinate_expand b
  have hc := parkerGolay_coordinate_expand c
  unfold parkerGolayTripleCoefficients parkerTripleIntersection
  simp only [ha, hb, hc, Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext p
    rw [Finset.sum_comm]
    arg 2
    ext j
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext p
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem parkerGolayFactorSet_associator (a b c : golay) :
    parkerGolayFactorSet a b + parkerGolayFactorSet (a + b) c +
      parkerGolayFactorSet b c + parkerGolayFactorSet a (b + c) =
        parkerTripleIntersection a b c := by
  rw [parkerGolayFactorSet_defect, parkerOrderedTheta_polarize,
    ← parkerTripleIntersection_basis_expand]
  · intro i j k
    exact parkerTripleIntersection_swap _ _ _
  · intro i j
    exact parkerTripleIntersection_repeat _ _

end Atlas.Fischer

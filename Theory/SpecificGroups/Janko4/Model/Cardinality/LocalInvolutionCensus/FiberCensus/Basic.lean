module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Counting
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Invariants for the four concrete max2 fibers

Conjugation inside the literal subgroup H preserves the pair of displacement
ranks of u and u*zH. The original source matrices give the same ranks because
sourceSubgroupEquivLocal is certified conjugation. The proposed eleven rank
pairs separate representatives within each prescribed quotient fiber; their
actual values remain a separate matrix certificate.

This lets an orbit forest and eleven small rank certificates bound the fibers,
without computing ranks for all 32768 coordinates or asserting that the
chosen actors generate a complete centralizer. Source motivation:
Aschbacher--Smith, refs/quasithin.pdf, printed pp.64--65, A.6.1--4.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus
open Coordinates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound

def sourceElement (j : Fin 4) (i : Fin 8192) : sourceSubgroup :=
  kernelProduct i * sourceLift j

noncomputable def element (j : Fin 4) (i : Fin 8192) : H :=
  localKernelProduct i * lift j

@[simp] theorem sourceEquiv_element (j : Fin 4) (i : Fin 8192) :
    sourceSubgroupEquivLocal (sourceElement j i) = element j i := by
  simp only [sourceElement, element, map_mul, localKernelProduct, lift]

def sourceRepresentative (i : Fin 11) : sourceSubgroup :=
  sourceElement (fiberIndex i) (kernelIndex i)

@[simp] theorem sourceEquiv_representative (i : Fin 11) :
    sourceSubgroupEquivLocal (sourceRepresentative i) = representative i :=
  sourceEquiv_element _ _

noncomputable def displacementRank (u : Model) : ℕ := (toMatrix u - 1).rank

private theorem matrix_displacement_conj (g u : Model) :
    toMatrix (g * u * g⁻¹) - 1 =
      toMatrix g * (toMatrix u - 1) * toMatrix g⁻¹ := by
  rw [map_mul, map_mul, mul_sub, sub_mul, mul_one,
    ← map_mul toMatrix g g⁻¹, mul_inv_cancel, map_one]

theorem displacementRank_conj (g u : Model) :
    displacementRank (g * u * g⁻¹) = displacementRank u := by
  unfold displacementRank
  rw [matrix_displacement_conj]
  have hu (v : Model) : IsUnit (toMatrix v).det := by
    exact ((Group.isUnit v).map toMatrix).map Matrix.detMonoidHom
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (hu g⁻¹),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (hu g)]

theorem displacementRank_of_isConj {u v : Model} (h : IsConj u v) :
    displacementRank u = displacementRank v := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (displacementRank_conj g u).symm

noncomputable def rankPair (u : H) : ℕ × ℕ :=
  (displacementRank (eH u), displacementRank (eH (u * zH)))

theorem rankPair_of_isConj {u v : H} (h : IsConj u v) : rankPair u = rankPair v := by
  exact Prod.ext (displacementRank_of_isConj (eH_isConj h))
    (displacementRank_of_isConj (eH_isConj (isConj_mul_zH h)))

noncomputable def sourceRankPair (u : sourceSubgroup) : ℕ × ℕ :=
  (displacementRank u, displacementRank ((u * sourceSeed ^ 2 : sourceSubgroup) : Model))

theorem rankPair_sourceEquiv (u : sourceSubgroup) :
    rankPair (sourceSubgroupEquivLocal u) = sourceRankPair u := by
  apply Prod.ext
  · change displacementRank (eH (sourceSubgroupEquivLocal u)) = _
    rw [eH_sourceSubgroupEquivLocal]
    simpa only [sourceRankPair, inv_inv] using displacementRank_conj h⁻¹ u
  · change displacementRank (eH (sourceSubgroupEquivLocal u * zH)) = _
    rw [← sourceEquiv_seed_sq, ← map_mul, eH_sourceSubgroupEquivLocal]
    simpa only [sourceRankPair, inv_inv] using displacementRank_conj h⁻¹
      ((u * sourceSeed ^ 2 : sourceSubgroup) : Model)

def expectedRanks : Fin 11 → ℕ × ℕ :=
  ![(0, 50), (50, 0), (50, 50), (56, 56), (56, 56), (50, 56),
    (56, 50), (50, 50), (56, 56), (56, 50), (50, 56)]

theorem expectedRanks_separate (i k : Fin 11)
    (hf : fiberIndex i = fiberIndex k) (hr : expectedRanks i = expectedRanks k) : i = k := by
  have hc : ∀ i k : Fin 11, fiberIndex i = fiberIndex k →
      expectedRanks i = expectedRanks k → i = k := by decide +kernel
  exact hc i k hf hr

def Required (i : Fin 11) : Prop := i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus

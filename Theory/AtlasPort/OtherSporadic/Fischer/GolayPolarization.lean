/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Fischer/GolayPolarization.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Fischer.ParkerGolayFactorSet

/-!
# Weight and overlap polarization for the Golay code

Integer coordinate counts and double evenness give the quarter-weight and
half-overlap polarization identities in the binary field.

Source: Gerald Höhn, ATLAS, `Atlas/Fischer/GolayPolarization.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Coordinate definitions are exposed for downstream reductions.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- Actual integer triple-intersection cardinality on the marked binary words. -/
def parkerTripleCount (a b c : BinaryWord) : ℕ :=
  ∑ i, if a i ≠ 0 ∧ b i ≠ 0 ∧ c i ≠ 0 then 1 else 0

theorem parkerTripleCount_cast (a b c : BinaryWord) :
    (parkerTripleCount a b c : Bit) = parkerTripleIntersection a b c := by
  classical
  rw [parkerTripleCount,Nat.cast_sum,parkerTripleIntersection]
  apply Finset.sum_congr rfl
  intro i _
  have he : ∀ x y z : Bit,
      ((if x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 then 1 else 0 : ℕ) : Bit)=x*y*z := by decide
  exact he _ _ _

theorem parkerOverlap_add (a b c : BinaryWord) :
    overlap (a+b) c + 2*parkerTripleCount a b c = overlap a c + overlap b c := by
  classical
  have he : ∀ x y z : Bit,
      (if x+y ≠ 0 ∧ z ≠ 0 then 1 else 0 : ℕ) +
        2*(if x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 then 1 else 0) =
      (if x ≠ 0 ∧ z ≠ 0 then 1 else 0) + (if y ≠ 0 ∧ z ≠ 0 then 1 else 0) := by decide
  simp only [overlap_eq_sum,parkerTripleCount,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => he (a i) (b i) (c i))

def golayQuarterWeight (a : golay) : Bit := (hammingNorm a.val / 4 : ℕ)
def golayHalfOverlap (a b : golay) : Bit := (overlap a.val b.val / 2 : ℕ)

theorem golay_overlap_two_dvd (a b : golay) : 2 ∣ overlap a.val b.val := by
  have h := golay_selfOrthogonal b.prop a.val a.prop
  rw [binaryDot_overlap, ZMod.natCast_eq_zero_iff_even] at h
  exact even_iff_two_dvd.mp h

theorem golayQuarterWeight_add (a b : golay) :
    golayQuarterWeight (a + b) = golayQuarterWeight a + golayQuarterWeight b +
      golayHalfOverlap a b := by
  have ha := golay_doublyEven a.val a.prop
  have hb := golay_doublyEven b.val b.prop
  have hab := golay_doublyEven (a + b).val (a + b).prop
  have ho := golay_overlap_two_dvd a b
  have he := binary_weight_add a.val b.val
  have hn : hammingNorm (a + b).val / 4 + overlap a.val b.val / 2 =
      hammingNorm a.val / 4 + hammingNorm b.val / 4 := by
    change hammingNorm (a.val + b.val) / 4 + _ = _
    omega
  have hc : golayQuarterWeight (a + b) + golayHalfOverlap a b =
      golayQuarterWeight a + golayQuarterWeight b := by
    simpa only [golayQuarterWeight, golayHalfOverlap, Nat.cast_add] using
      congrArg (fun n : ℕ => (n : Bit)) hn
  have h := congrArg (fun x : Bit => x + golayHalfOverlap a b) hc
  have hz : ∀ x : Bit, x + x = 0 := by decide
  simpa only [add_assoc, hz, add_zero] using h

theorem golayHalfOverlap_add_left (a b c : golay) :
    golayHalfOverlap (a + b) c = golayHalfOverlap a c + golayHalfOverlap b c +
      parkerTripleIntersection a.val b.val c.val := by
  have ha := golay_overlap_two_dvd a c
  have hb := golay_overlap_two_dvd b c
  have hab := golay_overlap_two_dvd (a + b) c
  have he := parkerOverlap_add a.val b.val c.val
  have hn : overlap (a + b).val c.val / 2 + parkerTripleCount a.val b.val c.val =
      overlap a.val c.val / 2 + overlap b.val c.val / 2 := by
    change overlap (a.val + b.val) c.val / 2 + _ = _
    omega
  have hc : golayHalfOverlap (a + b) c + parkerTripleIntersection a.val b.val c.val =
      golayHalfOverlap a c + golayHalfOverlap b c := by
    have hh := congrArg (fun n : ℕ => (n : Bit)) hn
    simpa only [Nat.cast_add, parkerTripleCount_cast, golayHalfOverlap] using hh
  have h := congrArg (fun x : Bit => x + parkerTripleIntersection a.val b.val c.val) hc
  have hz : ∀ x : Bit, x + x = 0 := by decide
  simpa only [add_assoc, hz, add_zero] using h

@[simp] theorem golayQuarterWeight_zero : golayQuarterWeight 0 = 0 := by
  simp [golayQuarterWeight]

@[simp] theorem golayHalfOverlap_zero_left (a : golay) : golayHalfOverlap 0 a = 0 := by
  simp [golayHalfOverlap, overlap]

theorem golayHalfOverlap_symmetric (a b : golay) :
    golayHalfOverlap a b = golayHalfOverlap b a := by
  unfold golayHalfOverlap
  congr 2
  simp only [overlap, and_comm]

end Atlas.Fischer

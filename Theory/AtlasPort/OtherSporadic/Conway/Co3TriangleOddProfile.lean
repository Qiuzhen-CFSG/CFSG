/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleOddProfile.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleGeometry
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalOddCoordinates
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleOddProfile.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem oddMinimumVector_sum (b : Omega) (c : golay) :
    (∑ i, (oddMinimumVector b c).val i) =
      20-2*(hammingNorm c.val : ℤ)+(if c.val b = 0 then 0 else 8) := by
  change (∑ i, signChange c.val (oddProfileBase {b} ∅) i) = _
  rw [signChange_sum,oddProfileBase_sum]
  have he : integerDot (oddProfileBase {b} ∅) (golayIntegerLift c.val) =
      (hammingNorm c.val : ℤ)-4*(if c.val b = 0 then 0 else 1) := by
    have hh (i : Omega) : oddProfileBase {b} ∅ i * golayIntegerLift c.val i =
        (if c.val i = 0 then 0 else 1) -
        (if i = b then 4*(if c.val b = 0 then 0 else 1) else 0) := by
      by_cases hi : i = b
      · subst i; simp [oddProfileBase,golayIntegerLift]; split_ifs <;> norm_num
      · simp [oddProfileBase,golayIntegerLift,hi]
    simp only [integerDot,hh,Finset.sum_sub_distrib]
    rw [hammingNorm_eq_sum]
    push_cast
    simp
  rw [he]
  simp only [Finset.card_singleton,Finset.card_empty,Nat.cast_one,Nat.cast_zero]
  split_ifs <;> ring

theorem normSix_oddMinimum_dot (a b : Omega) (c : golay) :
    integerDot (normSixVector a).val (oddMinimumVector b c).val =
      20-2*(hammingNorm c.val : ℤ)+(if c.val b = 0 then 0 else 8)+
      4*(if c.val a = 0 then (if a = b then -3 else 1) else (if a = b then 3 else -1)) := by
  rw [integerDot_normSix,oddMinimumVector_sum]
  congr 2
  simp [oddMinimumVector,signedOddProfile,signChange,oddProfileBase]
  split_ifs <;> norm_num

/-- Five intrinsic odd-coordinate types in the 2-3-4 triangle shell. -/
theorem co3_triangle_odd_cases (a b : Omega) (c : golay)
    (hd : integerDot (normSixVector a).val (oddMinimumVector b c).val = 8) :
    (b = a ∧ c = 0) ∨
    (b = a ∧ hammingNorm c.val = 16 ∧ c.val a = 1) ∨
    (b ≠ a ∧ hammingNorm c.val = 8 ∧ c.val a = 0 ∧ c.val b = 0) ∨
    (b ≠ a ∧ hammingNorm c.val = 12 ∧ c.val a = 0 ∧ c.val b = 1) ∨
    (b ≠ a ∧ hammingNorm c.val = 8 ∧ c.val a = 1 ∧ c.val b = 1) := by
  rw [normSix_oddMinimum_dot] at hd
  have hw := golay_weights c
  by_cases hab : b = a
  · subst b
    rcases bit_cases (c.val a) with hc | hc
    · have hz : hammingNorm c.val = 0 := by simp [hc] at hd; omega
      have hzero : c = 0 := Subtype.ext (hammingNorm_eq_zero.mp hz)
      exact Or.inl ⟨rfl,hzero⟩
    · right; left
      refine ⟨rfl,?_,hc⟩
      simp [hc] at hd; omega
  · rcases bit_cases (c.val a) with ha | ha <;> rcases bit_cases (c.val b) with hb | hb
    · exact Or.inr (Or.inr (Or.inl ⟨hab,by simp [ha,hb,Ne.symm hab] at hd; omega,ha,hb⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hab,by simp [ha,hb,Ne.symm hab] at hd; omega,ha,hb⟩)))
    · simp [ha,hb,Ne.symm hab] at hd
      change hammingNorm c.val = 0 ∨ hammingNorm c.val = 8 ∨ hammingNorm c.val = 12 ∨
        hammingNorm c.val = 16 ∨ hammingNorm c.val = 24 at hw
      omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hab,by simp [ha,hb,Ne.symm hab] at hd; omega,ha,hb⟩)))

end Atlas.Conway

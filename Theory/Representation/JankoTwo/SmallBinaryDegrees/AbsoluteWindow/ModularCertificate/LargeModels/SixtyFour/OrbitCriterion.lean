module
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Operations
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.RankOne

/-!
# Orbit bases from an acyclic generator graph

Each noninitial vector is a generator translate of an earlier vector. Induction
on its index constructs an algebra word carrying the seed to that vector.
The packed graph checker verifies both the decreasing indices and each actual
vector equation. Applying this to columns and rows supplies precisely the two
orbit hypotheses of the rank-one spanning theorem.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour
open Packed Matrix

abbrev Edges := Array (ℕ × Bool)

def checkOrbit (n : ℕ) (a b rows : Mat) (edges : Edges) : Bool :=
  (List.range n).all fun i => if i = 0 then true else
    decide (edges[i]!.1 < i) &&
      (rowProduct rows[edges[i]!.1]! (if edges[i]!.2 then b else a) n == rows[i]!)

variable {F : Type*} [Field F] [CharP F 2] {n : ℕ}

theorem orbit_steps [NeZero n] (t : F) (ht : t ^ 2 = t + 1) (a b rows : Mat) (edges : Edges)
    (h : checkOrbit n a b rows edges = true) (i : Fin n) (hi : i ≠ 0) :
    ∃ j : Fin n, j < i ∧ ∃ s : Bool,
      Matrix.vecMul (Packed.evalVector t n rows[j.val]!)
        (if s then eval t n b else eval t n a) = Packed.evalVector t n rows[i.val]! := by
  have hiz : i.val ≠ 0 := fun hz => hi (Fin.ext hz)
  have hc := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simp only [hiz, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hlt, hprod⟩ := hc
  let j : Fin n := ⟨edges[i.val]!.1, hlt.trans i.isLt⟩
  refine ⟨j, hlt, edges[i.val]!.2, ?_⟩
  have hm := Packed.eval_vecMul t ht n rows[j.val]!
    (if edges[i.val]!.2 then b else a) rows[i.val]! (eq_of_beq hprod)
  cases hs : edges[i.val]!.2 <;> simpa only [hs, Bool.false_eq_true, ↓reduceIte] using hm

omit [CharP F 2] in
theorem left_reachable [NeZero n] (S : Subalgebra F (Matrix (Fin n) (Fin n) F))
    (v : Fin n → F) (vs : Fin n → Fin n → F) (hzero : vs 0 = v)
    (hstep : ∀ i : Fin n, i ≠ 0 → ∃ j : Fin n, j < i ∧
      ∃ M ∈ S, M.mulVec (vs j) = vs i) (i : Fin n) :
    ∃ W ∈ S, W.mulVec v = vs i := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
    by_cases hi : i = 0
    · subst i
      exact ⟨1, S.one_mem, by simpa only [Matrix.one_mulVec] using hzero.symm⟩
    · obtain ⟨j, hj, M, hM, hm⟩ := hstep i hi
      obtain ⟨W, hW, hw⟩ := ih j hj
      refine ⟨M * W, S.mul_mem hM hW, ?_⟩
      rw [← Matrix.mulVec_mulVec, hw, hm]

omit [CharP F 2] in
theorem right_reachable [NeZero n] (S : Subalgebra F (Matrix (Fin n) (Fin n) F))
    (v : Fin n → F) (vs : Fin n → Fin n → F) (hzero : vs 0 = v)
    (hstep : ∀ i : Fin n, i ≠ 0 → ∃ j : Fin n, j < i ∧
      ∃ M ∈ S, Matrix.vecMul (vs j) M = vs i) (i : Fin n) :
    ∃ W ∈ S, Matrix.vecMul v W = vs i := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
    by_cases hi : i = 0
    · subst i
      exact ⟨1, S.one_mem, by simpa only [Matrix.vecMul_one] using hzero.symm⟩
    · obtain ⟨j, hj, M, hM, hm⟩ := hstep i hi
      obtain ⟨W, hW, hw⟩ := ih j hj
      refine ⟨W * M, S.mul_mem hW hM, ?_⟩
      rw [← Matrix.vecMul_vecMul, hw, hm]

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour

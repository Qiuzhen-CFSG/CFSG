module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.Orbits.MapRanges5

/-!
# Certified induced subgroup maps

The six checked ranges cover all 24192 points. They identify the two compact
maps with the complete literal left and right words. Repeated-word and append
identities then identify their iterates with the exact `subgroupWord`, including
both zero exponents and the specified left-then-right order.

Source: Coordinates/Model.lean and Coordinates/source/check_geometry.py.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry.Orbits

private theorem mapChecks (x : Point) : leftCheck x.val = true ∧ rightCheck x.val = true := by
  have h := (checkRange_append (start := 0) (n := 20480) (m := 3712) (checkRange_append (start := 0) (n := 16384) (m := 4096) (checkRange_append (start := 0) (n := 12288) (m := 4096) (checkRange_append (start := 0) (n := 8192) (m := 4096) (checkRange_append (start := 0) (n := 4096) (m := 4096) mapRange0 mapRange1) mapRange2) mapRange3) mapRange4) mapRange5)
  exact Bool.and_eq_true_iff.mp (checkRange_sound h (j := x.val) (by omega) (by omega))

theorem leftMove_eq (x : Point) :
    leftMove x = walk leftWord x := by
  have hx : run (leftWord.map Fin.val) x.val = entry 15 packedLeft x.val := by
    simpa only [leftCheck, beq_iff_eq] using (mapChecks x).1
  apply Fin.ext
  change entry 15 packedLeft x.val % 24192 = (walk leftWord x).val
  rw [← hx, run_eq_walk, Nat.mod_eq_of_lt (walk leftWord x).isLt]

theorem rightMove_eq (x : Point) :
    rightMove x = walk rightWord x := by
  have hx : run (rightWord.map Fin.val) x.val = entry 15 packedRight x.val := by
    simpa only [rightCheck, beq_iff_eq] using (mapChecks x).2
  apply Fin.ext
  change entry 15 packedRight x.val % 24192 = (walk rightWord x).val
  rw [← hx, run_eq_walk, Nat.mod_eq_of_lt (walk rightWord x).isLt]

lemma walk_append (u v : List (Fin 4)) (x : Point) :
    walk (u ++ v) x = walk v (walk u x) := by
  simp only [walk, List.foldl_append]

lemma walk_replicate (w : List (Fin 4)) (n : ℕ) (x : Point) :
    walk (List.replicate n w).flatten x = (walk w)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, walk_append, ih,
      Function.iterate_succ_apply]

theorem walk_subgroup_cached
    (t : CoefficientTheory.PowerIndex) (x : Point) :
    walk (subgroupWord t) x = cachedSubgroup t x := by
  have hleft : leftMove = walk leftWord := funext leftMove_eq
  have hright : rightMove = walk rightWord := funext rightMove_eq
  simp only [subgroupWord, walk_append, walk_replicate, cachedSubgroup, hleft, hright]

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry.Orbits

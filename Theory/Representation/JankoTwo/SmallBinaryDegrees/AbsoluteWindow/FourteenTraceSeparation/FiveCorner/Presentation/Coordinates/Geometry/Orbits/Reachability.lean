module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.Orbits.OrbitRanges2

/-!
# Every fixed orbit point is reached by its subgroup-power word

The retained pair of exponents is checked using the certified subgroup maps,
and walk_subgroup_cached transports each result to the unchanged literal walk.
The root and orbit label are those of Coordinates/Model.lean.

Source: Coordinates/source/discovery/orbit-subgroup-powers.json and
Coordinates/source/check_geometry.py.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry.Orbits

private theorem orbitChecks : checkRange orbitCheck 0 24192 = true :=
  checkRange_append (start := 0) (n := 16384) (m := 7808)
    (checkRange_append (start := 0) (n := 8192) (m := 8192) orbitRange0 orbitRange1) orbitRange2

theorem orbits
    (x : Point) : ∃ t : CoefficientTheory.PowerIndex,
    walk (subgroupWord t) (root (orbit x)) = x := by
  have hx : (⟨x.val % 24192, Nat.mod_lt _ (by decide)⟩ : Point) = x :=
    Fin.ext (Nat.mod_eq_of_lt x.isLt)
  have h := checkRange_sound orbitChecks (j := x.val) (by omega) (by omega)
  simp only [orbitCheck, hx, fastRoot_eq, fastOrbit_eq, beq_iff_eq] at h
  refine ⟨powers x, ?_⟩
  rw [walk_subgroup_cached]
  exact Fin.ext h

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry.Orbits

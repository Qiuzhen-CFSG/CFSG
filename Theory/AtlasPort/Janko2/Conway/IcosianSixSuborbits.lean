/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianSixSuborbits.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianAxisOrbitLinks
public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointShapeNormCounts

/-!
# IcosianSixSuborbits

The nine local shape-and-norm pieces fuse into six full axis-stabilizer orbits.
Explicit orbit links prove that equal coordinate norm is the exact orbit criterion.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianSixSuborbits.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- A calculation on the nine labelled local pieces, not on root points. -/
theorem icosianNineNormFusion_cases : ∀ i j : Fin 9,
    icosianNineLocalNormValues i=icosianNineLocalNormValues j →
    icosianNineLocalShapeIndices i=icosianNineLocalShapeIndices j ∨
    (icosianNineLocalShapeIndices i=0 ∧ icosianNineLocalShapeIndices j=1 ∧ icosianNineLocalNormValues i=0) ∨
    (icosianNineLocalShapeIndices i=1 ∧ icosianNineLocalShapeIndices j=0 ∧ icosianNineLocalNormValues i=0) ∨
    (icosianNineLocalShapeIndices i=1 ∧ icosianNineLocalShapeIndices j=2 ∧ icosianNineLocalNormValues i=2) ∨
    (icosianNineLocalShapeIndices i=2 ∧ icosianNineLocalShapeIndices j=1 ∧ icosianNineLocalNormValues i=2) ∨
    (icosianNineLocalShapeIndices i=2 ∧ icosianNineLocalShapeIndices j=3 ∧ icosianNineLocalNormValues i=1) ∨
    (icosianNineLocalShapeIndices i=3 ∧ icosianNineLocalShapeIndices j=2 ∧ icosianNineLocalNormValues i=1) := by
  decide +kernel

theorem icosianSameAxisOrbit_of_norm (p q : IcosianRootPoint)
    (hn : icosianRootPointNormWord p 0=icosianRootPointNormWord q 0) :
    IcosianSameAxisOrbit p q := by
  obtain ⟨i,hpi,hni⟩ := icosianRootPointShapeNormLevel_nine_exhaustive p
  obtain ⟨j,hqj,hnj⟩ := icosianRootPointShapeNormLevel_nine_exhaustive q
  have hv := hni.symm.trans (hn.trans hnj)
  rcases icosianNineNormFusion_cases i j hv with hs | ⟨hi,hj,hv⟩ | ⟨hi,hj,hv⟩ |
    ⟨hi,hj,hv⟩ | ⟨hi,hj,hv⟩ | ⟨hi,hj,hv⟩ | ⟨hi,hj,hv⟩
  · exact icosianSameAxisOrbit_of_shape_norm _ p q hpi (hs.symm ▸ hqj) hn
  all_goals
    rw [hi] at hpi
    rw [hj] at hqj
  · exact icosianAxisOrbit_A_B p q hpi hqj (hni.trans hv) (hn.symm.trans (hni.trans hv))
  · exact (icosianAxisOrbit_A_B q p hqj hpi (hn.symm.trans (hni.trans hv)) (hni.trans hv)).symm
  · exact icosianAxisOrbit_B_C p q hpi hqj (hni.trans hv) (hn.symm.trans (hni.trans hv))
  · exact (icosianAxisOrbit_B_C q p hqj hpi (hn.symm.trans (hni.trans hv)) (hni.trans hv)).symm
  · exact icosianAxisOrbit_C_D p q hpi hqj (hni.trans hv) (hn.symm.trans (hni.trans hv))
  · exact (icosianAxisOrbit_C_D q p hqj hpi (hn.symm.trans (hni.trans hv)) (hni.trans hv)).symm

/-- The six intrinsic coordinate norm levels are exactly the orbits of the
full stabilizer of the first quaternionic root line. -/
theorem icosianFullAxisStabilizer_orbit (p : IcosianRootPoint) :
    MulAction.orbit icosianFullAxisStabilizer p=
      {q : IcosianRootPoint | icosianRootPointNormWord q 0=icosianRootPointNormWord p 0} := by
  ext q
  constructor
  · rintro ⟨g,rfl⟩
    exact icosianAxisStabilizer_point_norm g.val g.property p
  · intro hn
    exact MulAction.orbit_eq_iff.mp (icosianSameAxisOrbit_of_norm p q hn.symm).symm

theorem icosianFullAxisStabilizer_orbit_card (i : Fin 6) (p : IcosianRootPoint)
    (hp : icosianRootPointNormWord p 0=icosianRootCoordinateLevels i) :
    Nat.card (MulAction.orbit icosianFullAxisStabilizer p)=![1,10,160,80,32,32] i := by
  rw [Nat.card_congr (Equiv.setCongr (icosianFullAxisStabilizer_orbit p)),hp]
  exact icosianRootPointNormLevel_six_card i

end Atlas.Conway

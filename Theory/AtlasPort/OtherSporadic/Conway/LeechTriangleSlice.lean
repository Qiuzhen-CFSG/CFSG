/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/LeechTriangleSlice.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3HeptadDot
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechIntegralPairing

/-!
Leech lattice slices with prescribed norm and two pairings.
Isometries fixing both marked vectors preserve the slice; the lattice minimum bounds pairings.

Source: Gerald Höhn, `Atlas/Conway/LeechTriangleSlice.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

/-- A norm and two pairing conditions in the retained lattice. -/
def LeechTriangleSlice (x a : leech) (r s t : ℤ) :=
  {y : leech // integerDot y.val y.val = r ∧
    integerDot x.val y.val = s ∧ integerDot a.val y.val = t}

abbrev LeechTriangleStabilizer (x a : leech) :=
  MulAction.stabilizer (fullVectorStabilizer x) a

instance leechTriangleSliceAction (x a : leech) (r s t : ℤ) :
    MulAction (LeechTriangleStabilizer x a) (LeechTriangleSlice x a r s t) where
  smul g y := ⟨g.val.val.val y.val,by
    have hx : g.val.val.val x = x := g.val.prop
    have ha : g.val.val.val a = a := g.prop
    refine ⟨(g.val.val.prop _ _).trans y.prop.1,?_,?_⟩
    · have hh := g.val.val.prop x y.val
      rw [hx] at hh
      exact hh.trans y.prop.2.1
    · have hh := g.val.val.prop a y.val
      rw [ha] at hh
      exact hh.trans y.prop.2.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem leech_minimum_pair_dot_le (u v : leech)
    (hu : integerDot u.val u.val = 32) (hv : integerDot v.val v.val = 32)
    (hne : u ≠ v) : integerDot u.val v.val ≤ 16 := by
  have hh : (u-v).val ≠ 0 := by
    intro h
    apply hne
    exact sub_eq_zero.mp (Subtype.ext h : u-v = 0)
  have hm := leech_raw_minimum (u-v).val (u-v).prop hh
  change 32 ≤ integerDot (u.val-v.val) (u.val-v.val) at hm
  rw [integerDot_sub_left,integerDot_sub_right,integerDot_sub_right,
    integerDot_comm v.val u.val,hu,hv] at hm
  omega

theorem leech_norm_sub (x y : leech) :
    integerDot (x-y).val (x-y).val = integerDot x.val x.val +
      integerDot y.val y.val - 2*integerDot x.val y.val := by
  change integerDot (x.val-y.val) (x.val-y.val) = _
  rw [integerDot_sub_left,integerDot_sub_right,integerDot_sub_right,integerDot_comm y.val x.val]
  ring

end Atlas.Conway

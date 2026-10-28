/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3MathieuOrbits.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu22PointStabilizer
public import Theory.AtlasPort.OtherSporadic.Conway.Co3PointHeptadAction
public import Theory.AtlasPort.OtherSporadic.Mathieu.GolayMarkedOctadTransitivity
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3MathieuOrbits.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem co3_points_mathieu_transitive (a : Omega) (b c : Mathieu23Points a) :
    ∃ g : Mathieu23PointModel a,
      co3PointHeptadMap a g (Sum.inl b) = Sum.inl c := by
  let := mathieu23_pretransitive a
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Mathieu23PointModel a) b c
  exact ⟨g,congrArg Sum.inl hg⟩

theorem co3_heptads_mathieu_transitive (a : Omega)
    (B C : {B // B ∈ mathieu23Blocks a}) :
    ∃ g : Mathieu23PointModel a,
      co3PointHeptadMap a g (Sum.inr B) = Sum.inr C := by
  obtain ⟨g,hg,hO⟩ := mathieu24_marked_octad_transitive {a}
    (insert a (mathieu23BlockLift a B.val)) (insert a (mathieu23BlockLift a C.val))
    (by simp) ((mathieu23Blocks_mem a B.val).mp B.prop)
    ((mathieu23Blocks_mem a C.val).mp C.prop) (by simp) (by simp)
  let p : Mathieu23PointModel a := ⟨g,hg a (by simp)⟩
  refine ⟨p,congrArg Sum.inr (Subtype.ext ?_)⟩
  ext i
  have h := Iff.of_eq (congrArg (fun T : Finset Omega => i.val ∈ T) hO)
  have hh : insert a (mathieu23BlockLift a (mathieu23PermuteBlock a p B.val)) =
      permuteBlock g.val (insert a (mathieu23BlockLift a B.val)) := by
    rw [mathieu23BlockLift_permute]
    have ha : g.val a = a := hg a (by simp)
    simp [permuteBlock,p,ha]
  rw [← hh] at h
  simpa [mathieu23BlockLift,(show i.val ≠ a from i.prop)] using h

theorem co3_mathieu_two_orbits (a : Omega) (p q : Co3PointHeptad a) :
    (∃ g : Mathieu23PointModel a, co3PointHeptadMap a g p = q) ↔
      (∃ b c, p = Sum.inl b ∧ q = Sum.inl c) ∨
      (∃ B C, p = Sum.inr B ∧ q = Sum.inr C) := by
  constructor
  · rintro ⟨g,rfl⟩
    cases p with
    | inl b => exact Or.inl ⟨b,g • b,rfl,rfl⟩
    | inr B => exact Or.inr ⟨B,_,rfl,rfl⟩
  · rintro (⟨b,c,rfl,rfl⟩ | ⟨B,C,rfl,rfl⟩)
    · exact co3_points_mathieu_transitive a b c
    · exact co3_heptads_mathieu_transitive a B C

end Atlas.Conway

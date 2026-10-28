/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianRootPointOrthogonality.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointAction

/-!
# IcosianRootPointOrthogonality

The Hermitian form defines a symmetric, irreflexive orthogonality relation on root
points. Its invariant three-point cliques are the actual root frames.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianRootPointOrthogonality.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- Orthogonality of actual quaternionic root lines, independent of representatives. -/
def IcosianRootPointOrthogonal (p q : IcosianRootPoint) : Prop :=
  ∀ r s : IcosianRoot,icosianRootToPoint r=p → icosianRootToPoint s=q →
    icosianHermitian (icosianCoordinateEmbedding r.val) (icosianCoordinateEmbedding s.val)=0

theorem icosianRootPointOrthogonal_iff (r s : IcosianRoot) :
    IcosianRootPointOrthogonal (icosianRootToPoint r) (icosianRootToPoint s) ↔
      icosianHermitian (icosianCoordinateEmbedding r.val) (icosianCoordinateEmbedding s.val)=0 := by
  constructor
  · intro h; exact h r s rfl rfl
  · intro h a b ha hb
    obtain ⟨u,rfl⟩ := (icosianRootPoint_eq_iff r a).mp (congrArg Subtype.val ha)
    obtain ⟨v,rfl⟩ := (icosianRootPoint_eq_iff s b).mp (congrArg Subtype.val hb)
    change icosianHermitian
      (icosianRightMul (icosianCoordinateEmbedding r.val) u.val.val)
      (icosianRightMul (icosianCoordinateEmbedding s.val) v.val.val)=0
    rw [icosianHermitian_rightMul_left,icosianHermitian_rightMul_right,h]
    simp

theorem icosianRootPointOrthogonal_symm {p q : IcosianRootPoint}
    (h : IcosianRootPointOrthogonal p q) : IcosianRootPointOrthogonal q p := by
  intro r s hr hs
  rw [← icosianHermitian_star,h s r hs hr,star_zero]

theorem icosianRootPointOrthogonal_irrefl (p : IcosianRootPoint) :
    ¬IcosianRootPointOrthogonal p p := by
  intro h
  obtain ⟨r,hr⟩ := icosianRootToPoint_surjective p
  have hz := h r r hr hr
  rw [r.property.2] at hz
  have hh := congrArg (fun z : IcosianQuaternion => z.re.re) hz
  norm_num [QuaternionAlgebra.re_ofNat,QuadraticAlgebra.re_ofNat] at hh

theorem icosianRootPointOrthogonal_smul_iff (g : icosianHermitianGroup)
    (p q : IcosianRootPoint) :
    IcosianRootPointOrthogonal (g • p) (g • q) ↔ IcosianRootPointOrthogonal p q := by
  obtain ⟨r,rfl⟩ := icosianRootToPoint_surjective p
  obtain ⟨s,rfl⟩ := icosianRootToPoint_surjective q
  rw [← icosianRootToPoint_smul,← icosianRootToPoint_smul,
    icosianRootPointOrthogonal_iff,icosianRootPointOrthogonal_iff]
  change icosianHermitian (icosianCoordinateEmbedding (icosianHermitianRoot g r).val)
    (icosianCoordinateEmbedding (icosianHermitianRoot g s).val)=0 ↔ _
  rw [icosianHermitianRoot_embedding,icosianHermitianRoot_embedding,g.property.2.1]

/-- Actual unordered orthogonal triples of quaternionic root lines. -/
def IcosianRootFrame := {F : Finset IcosianRootPoint // F.card=3 ∧
  (↑F : Set IcosianRootPoint).Pairwise IcosianRootPointOrthogonal}

end Atlas.Conway

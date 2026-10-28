/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianRootPointAction.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointCount

/-!
# IcosianRootPointAction

Hermitian lattice maps preserve the root set and its scalar-line equivalence. The
resulting root and root-point actions agree with the concrete linear action.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianRootPointAction.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- The full Hermitian group maps actual roots to actual roots. -/
theorem icosianHermitian_root_image (g : icosianHermitianGroup) (r : IcosianRoot) :
    ∃ s : IcosianRoot,icosianCoordinateEmbedding s.val=g.val (icosianCoordinateEmbedding r.val) := by
  have hr : icosianCoordinateEmbedding r.val∈rationalIcosianLattice :=
    (rationalIcosianLattice_mem _).mpr ⟨r.val,r.property.1,rfl⟩
  obtain ⟨s,hs,he⟩ := (rationalIcosianLattice_mem _).mp ((g.property.2.2 _).mp hr)
  refine ⟨⟨s,hs,?_⟩,he⟩
  rw [he,g.property.2.1,r.property.2]

def icosianHermitianRoot (g : icosianHermitianGroup) (r : IcosianRoot) : IcosianRoot :=
  (icosianHermitian_root_image g r).choose

theorem icosianHermitianRoot_embedding (g : icosianHermitianGroup) (r : IcosianRoot) :
    icosianCoordinateEmbedding (icosianHermitianRoot g r).val=
      g.val (icosianCoordinateEmbedding r.val) :=
  (icosianHermitian_root_image g r).choose_spec

theorem icosianRoot_embedding_injective :
    Function.Injective (fun r : IcosianRoot => icosianCoordinateEmbedding r.val) := by
  intro r s h
  exact Subtype.ext (icosianCoordinateEmbedding_injective h)

instance icosianHermitian_root_mulAction : MulAction icosianHermitianGroup IcosianRoot where
  smul := icosianHermitianRoot
  one_smul r := by
    apply icosianRoot_embedding_injective
    change icosianCoordinateEmbedding (icosianHermitianRoot 1 r).val=icosianCoordinateEmbedding r.val
    rw [icosianHermitianRoot_embedding]
    rfl
  mul_smul g h r := by
    apply icosianRoot_embedding_injective
    change icosianCoordinateEmbedding (icosianHermitianRoot (g*h) r).val=
      icosianCoordinateEmbedding (icosianHermitianRoot g (icosianHermitianRoot h r)).val
    rw [icosianHermitianRoot_embedding,icosianHermitianRoot_embedding,icosianHermitianRoot_embedding]
    rfl

theorem icosianRootPoint_smul (g : icosianHermitianGroup) (r : IcosianRoot) :
    icosianRootPoint (g • r)=g • icosianRootPoint r := by
  change Projectivization.mk _ (icosianCoordinateEmbedding (icosianHermitianRoot g r).val) _=_
  apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
  refine ⟨1,?_⟩
  change (1 : IcosianQuaternionᵐᵒᵖ) • g.val (icosianCoordinateEmbedding r.val)=icosianCoordinateEmbedding (icosianHermitianRoot g r).val
  rw [one_smul]
  exact (icosianHermitianRoot_embedding g r).symm

instance icosianHermitian_rootPoint_mulAction : MulAction icosianHermitianGroup IcosianRootPoint where
  smul g p := ⟨g • p.val,by
    obtain ⟨r,hr⟩ := p.property
    exact ⟨g • r,(icosianRootPoint_smul g r).trans (congrArg (g • ·) hr)⟩⟩
  one_smul p := Subtype.ext (one_smul _ _)
  mul_smul g h p := Subtype.ext (mul_smul _ _ _)

@[simp] theorem icosianRootToPoint_smul (g : icosianHermitianGroup) (r : IcosianRoot) :
    icosianRootToPoint (g • r)=g • icosianRootToPoint r :=
  Subtype.ext (icosianRootPoint_smul g r)

end Atlas.Conway

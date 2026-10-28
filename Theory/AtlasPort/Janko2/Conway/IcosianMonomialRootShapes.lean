/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianMonomialRootShapes.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointShapes
public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointAction
public import Theory.AtlasPort.Janko2.Conway.IcosianFullFrameStabilizer

/-!
# IcosianMonomialRootShapes

Monomial transformations preserve root shapes by permuting coordinate norms. The full
frame-stabilizer description transfers this invariance to its root-point action.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianMonomialRootShapes.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianMonomialRoot_coordinates (g : icosianLiftedMonomial) (r : IcosianRoot)
    (i : Fin 3) : ((icosianMonomialToHermitian g • r).val i).val=
      (g.val.left i).val.val*(r.val (g.val.right.symm i)).val := by
  have h := congrFun (icosianHermitianRoot_embedding (icosianMonomialToHermitian g) r) i
  exact h

theorem icosianMonomialRoot_norm_word (g : icosianLiftedMonomial) (r : IcosianRoot)
    (i : Fin 3) : icosianRootNormWord (icosianMonomialToHermitian g • r) i=
      icosianRootNormWord r (g.val.right.symm i) := by
  apply goldenIntegerToRational_injective
  simp only [icosianRootNormWord,icosianIntegralNorm_spec]
  rw [icosianMonomialRoot_coordinates,icosianNorm_mul,icosianNormOneGroup_norm,one_mul]

theorem icosianMonomialRoot_shape (g : icosianLiftedMonomial) (r : IcosianRoot)
    (i : Fin 4) : HasIcosianRootShape (icosianMonomialToHermitian g • r) i ↔
      HasIcosianRootShape r i := by
  have hp := Atlas.triple_perm_reindex g.val.right (icosianRootNormWord r)
  simp only [HasIcosianRootShape,icosianMonomialRoot_norm_word]
  exact ⟨fun h => hp.symm.trans h,fun h => hp.trans h⟩

theorem icosianCoordinateFrame_root_shape (g : icosianCoordinateFrameStabilizer)
    (r : IcosianRoot) (i : Fin 4) : HasIcosianRootShape (g.val • r) i ↔
      HasIcosianRootShape r i := by
  obtain ⟨m,hm⟩ := (show g.val∈icosianMonomialToHermitian.range from
    icosianMonomial_range_eq_frameStabilizer.symm ▸ g.property)
  rw [← hm]
  exact icosianMonomialRoot_shape m r i

theorem icosianCoordinateFrame_rootPoint_shape (g : icosianCoordinateFrameStabilizer)
    (p : IcosianRootPoint) (i : Fin 4) : HasIcosianRootPointShape (g.val • p) i ↔
      HasIcosianRootPointShape p i := by
  have hf (g : icosianCoordinateFrameStabilizer) (p : IcosianRootPoint)
      (hp : HasIcosianRootPointShape p i) : HasIcosianRootPointShape (g.val • p) i := by
    obtain ⟨r,hr,hi⟩ := hp
    refine ⟨g.val • r,?_,(icosianCoordinateFrame_root_shape g r i).mpr hi⟩
    exact (icosianRootPoint_smul _ _).trans (congrArg (g.val • ·) hr)
  refine ⟨fun h => ?_,hf g p⟩
  have h' := hf g⁻¹ (g.val • p) h
  simpa only [Subgroup.coe_inv,inv_smul_smul] using h'

end Atlas.Conway

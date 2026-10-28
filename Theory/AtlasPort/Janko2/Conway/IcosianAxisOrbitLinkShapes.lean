/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianAxisOrbitLinkShapes.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianAxisSuborbitLinks
public import Theory.AtlasPort.Janko2.Conway.IcosianAxisOrbitRelation

/-!
# IcosianAxisOrbitLinkShapes

The explicit axis-fixing transition words link the local root shapes. Coordinate and
norm evaluations certify the input and output labels.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianAxisOrbitLinkShapes.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- Permuting coordinates preserves the already classified integral norm shape. -/
theorem icosianRootPermute_shape (s : Equiv.Perm (Fin 3)) (r : IcosianRoot) (a : Fin 4)
    (h : HasIcosianRootShape r a) : HasIcosianRootShape (icosianRootPermute s r) a := by
  exact (Atlas.triple_perm_reindex s (icosianRootNormWord r)).trans h

theorem icosianAxisLinkBInput_shape : HasIcosianRootShape icosianAxisLinkBInput 1 :=
  icosianRootPermute_shape _ _ _ icosianLocalBRoot_shape

theorem icosianAxisLinkCInput_shape : HasIcosianRootShape icosianAxisLinkCInput 2 :=
  icosianRootPermute_shape _ _ _ icosianLocalCRoot_shape

theorem icosianAxisLinkBInput_norm : icosianRootNormWord icosianAxisLinkBInput 0=2 := by
  change icosianRootNormWord icosianLocalBRoot ((Equiv.swap 0 1).symm 0)=2
  simp [icosianLocalBRoot_word]

theorem icosianAxisLinkCInput_norm : icosianRootNormWord icosianAxisLinkCInput 0=1 := by
  change icosianRootNormWord icosianLocalCRoot ((Equiv.swap 0 1).symm 0)=1
  simp [icosianLocalCRoot_word]

theorem icosianAxisLinkBImage_word (j : Fin 3) :
    icosianRootNormWord (icosianAxisTransitionWord 0 • icosianAxisLinkBInput) j=
      (![2,1,1] j) := by
  apply icosianRootNormWord_of_norm
  have he := congrFun (icosianHermitianRoot_embedding (icosianAxisTransitionWord 0)
    icosianAxisLinkBInput) j
  change icosianNorm ((icosianHermitianRoot (icosianAxisTransitionWord 0)
    icosianAxisLinkBInput).val j).val=_
  change ((icosianHermitianRoot (icosianAxisTransitionWord 0) icosianAxisLinkBInput).val j).val=
    (icosianAxisTransitionWord 0).val (icosianCoordinateEmbedding icosianAxisLinkBInput.val) j at he
  rw [he,icosianAxisTransition_B_C_norm]
  fin_cases j <;> simp [map_ofNat]

theorem icosianAxisLinkCImage_word (j : Fin 3) :
    icosianRootNormWord (icosianAxisTransitionWord 1 • icosianAxisLinkCInput) j=
      (![1,QuadraticAlgebra.omega^2,(1-QuadraticAlgebra.omega)^2] j) := by
  apply icosianRootNormWord_of_norm
  have he := congrFun (icosianHermitianRoot_embedding (icosianAxisTransitionWord 1)
    icosianAxisLinkCInput) j
  change icosianNorm ((icosianHermitianRoot (icosianAxisTransitionWord 1)
    icosianAxisLinkCInput).val j).val=_
  change ((icosianHermitianRoot (icosianAxisTransitionWord 1) icosianAxisLinkCInput).val j).val=
    (icosianAxisTransitionWord 1).val (icosianCoordinateEmbedding icosianAxisLinkCInput.val) j at he
  rw [he,icosianAxisTransition_C_D_norm]
  fin_cases j <;> decide +kernel

theorem icosianAxisLinkBImage_shape :
    HasIcosianRootShape (icosianAxisTransitionWord 0 • icosianAxisLinkBInput) 2 := by
  change [icosianRootNormWord _ 0,icosianRootNormWord _ 1,icosianRootNormWord _ 2].Perm [1,1,2]
  simp only [icosianAxisLinkBImage_word]
  exact (List.Perm.swap 1 2 [1]).trans (List.Perm.cons 1 (List.Perm.swap 1 2 []))

theorem icosianAxisLinkCImage_shape :
    HasIcosianRootShape (icosianAxisTransitionWord 1 • icosianAxisLinkCInput) 3 := by
  change [icosianRootNormWord _ 0,icosianRootNormWord _ 1,icosianRootNormWord _ 2].Perm
    [1,QuadraticAlgebra.omega^2,(1-QuadraticAlgebra.omega)^2]
  simp only [icosianAxisLinkCImage_word]
  exact List.Perm.refl _

end Atlas.Conway

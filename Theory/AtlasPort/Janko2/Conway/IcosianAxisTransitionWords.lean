/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianAxisTransitionWords.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianAxisTransitionData
public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionGeneratedElements
public import Theory.AtlasPort.Janko2.Conway.IcosianAxisReflections

/-!
# IcosianAxisTransitionWords

Products of actual root reflections define the axis transition words. Their subgroup
membership and pointwise formulas connect the group action to coordinate
calculations.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianAxisTransitionWords.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

def icosianAxisTransitionBase (k : Fin 3) : icosianHermitianGroup :=
  icosianAxisTransitionGenerator 0 * icosianAxisTransitionGenerator ⟨k.val+1,by omega⟩ *
    icosianAxisReflection 1 * icosianAxisTransitionGenerator 0

def icosianAxisTransitionWord (k : Fin 4) : icosianHermitianGroup :=
  if h : k.val<3 then icosianAxisTransitionBase ⟨k.val,h⟩
  else icosianReflectionEdgeWord 1 0 * icosianAxisTransitionBase 0

theorem icosianAxisTransitionGenerator_mem (k : Fin 4) :
    icosianAxisTransitionGenerator k∈icosianReflectionGroup :=
  icosianRootReflection_mem _ _ _

theorem icosianAxisTransitionBase_mem (k : Fin 3) :
    icosianAxisTransitionBase k∈icosianReflectionGroup :=
  icosianReflectionGroup.mul_mem (icosianReflectionGroup.mul_mem
    (icosianReflectionGroup.mul_mem (icosianAxisTransitionGenerator_mem 0)
      (icosianAxisTransitionGenerator_mem _)) (icosianAxisReflection_mem 1))
    (icosianAxisTransitionGenerator_mem 0)

theorem icosianAxisTransitionWord_mem (k : Fin 4) :
    icosianAxisTransitionWord k∈icosianReflectionGroup := by
  unfold icosianAxisTransitionWord
  split
  · exact icosianAxisTransitionBase_mem _
  · exact icosianReflectionGroup.mul_mem (icosianReflectionEdgeWord_mem_reflections 1 0)
      (icosianAxisTransitionBase_mem 0)

def icosianAxisTransitionBaseRaw (k : Fin 3) (x : IcosianRationalCoordinates) :
    IcosianRationalCoordinates :=
  icosianReflection (icosianAxisTransitionRoot 0)
    (icosianReflection (icosianAxisTransitionRoot ⟨k.val+1,by omega⟩)
      (fun j => if j=1 then -(icosianReflection (icosianAxisTransitionRoot 0) x j)
        else icosianReflection (icosianAxisTransitionRoot 0) x j))

def icosianAxisTransitionRaw (k : Fin 4) (x : IcosianRationalCoordinates) :
    IcosianRationalCoordinates :=
  if h : k.val<3 then icosianAxisTransitionBaseRaw ⟨k.val,h⟩ x
  else icosianReflectionEdgeDiagonalRaw 1 0 (icosianAxisTransitionBaseRaw 0 x)

theorem icosianAxisTransitionGenerator_apply (k : Fin 4) (x : IcosianRationalCoordinates) :
    (icosianAxisTransitionGenerator k).val x=icosianReflection (icosianAxisTransitionRoot k) x := rfl

theorem icosianAxisTransitionBase_apply (k : Fin 3) (x : IcosianRationalCoordinates) :
    (icosianAxisTransitionBase k).val x=icosianAxisTransitionBaseRaw k x := by
  simp only [icosianAxisTransitionBase,Subgroup.coe_mul,LinearEquiv.mul_apply,
    icosianAxisTransitionGenerator_apply,icosianAxisTransitionBaseRaw]
  congr 2
  funext j
  exact icosianAxisReflection_apply 1 j _

theorem icosianAxisTransitionWord_apply (k : Fin 4) (x : IcosianRationalCoordinates) :
    (icosianAxisTransitionWord k).val x=icosianAxisTransitionRaw k x := by
  unfold icosianAxisTransitionWord icosianAxisTransitionRaw
  split
  · exact icosianAxisTransitionBase_apply _ _
  · simp only [Subgroup.coe_mul,LinearEquiv.mul_apply,icosianAxisTransitionBase_apply,
      icosianReflectionEdgeWord_linear]
    funext j
    exact icosianReflectionEdgeMonomial_apply _ _ _ _

end Atlas.Conway

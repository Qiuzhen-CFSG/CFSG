module
public import CFSG.Quasithin.ChapterF.Section05.ModelVertexCore
public import CFSG.Quasithin.ChapterF.Section05.ModelVertexComplement
import all CFSG.Quasithin.ChapterF.Section05.ModelVertexComplement
/-!
# Original source core and complement under the marked vertex map

Agreement with the literal plane endpoint identifies the original E2 and A2
with their native subgroups. The checked model comparison then sends A2 to
the local two-core and the independent source complement to the literal second
factor, both as subgroups of the vertex stabilizer. These are the markings
needed by the F.5.7 overlap adjustment; the source endpoint agreement is kept
as the explicit input supplied by source completion recognition.

Source: Aschbacher--Smith F.5.7, printed p.303.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05
open GreenBook.LieModels.UnitaryFour
open ExceptionalLocal OmegaSixThree
public noncomputable section
local notation "hn" => Nat.le_refl 1
local notation "X" => Extension.ProjectiveExtension 1 hn
local notation "V" => OmegaSixThree.OrthogonalityGraph.modelSystem.vertexGroup
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

/-- The exact source complement already lies in E2, using only the original
faithful endpoint map. -/
theorem sourceLocalComplement_le_planeGraph (hi : Function.Injective i) :
    sourceLocalComplement c i≤E c i true := by
  rw [sourceLocalComplement,E_eq_map_centralizer c i hi true]
  apply map_mono
  intro a ha
  apply mem_centralizer_singleton_iff.mpr
  exact Subtype.ext (mem_centralizer_singleton_iff.mp
    (nativeLocalComplement_le_graphCentralizer ha).2)

/-- In particular the concrete source complement belongs to the original H. -/
theorem sourceLocalComplement_le_H (hi : Function.Injective i) :
    sourceLocalComplement c i≤H c i :=
  (sourceLocalComplement_le_planeGraph c i hi).trans (E_plane_le_H c i)

theorem source_plane_graphCentralizer_eq_map (hi : Function.Injective i) (j : X →* G)
    (hj : ∀ a : Extension.plane 1 hn,j a.val=i (c.right a)) :
    E c i true=nativePlaneGraphCentralizer.map j := by
  rw [E_eq_map_centralizer c i hi true]
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    refine ⟨a.val,⟨a.property,mem_centralizer_singleton_iff.mpr ?_⟩,hj a⟩
    exact congrArg (fun b : modelEndpoint true => b.val) (mem_centralizer_singleton_iff.mp ha)
  · rintro _ ⟨a,ha,rfl⟩
    refine ⟨⟨a,ha.1⟩,mem_centralizer_singleton_iff.mpr ?_,(hj _).symm⟩
    exact Subtype.ext (mem_centralizer_singleton_iff.mp ha.2)

theorem source_plane_core_eq_map (hi : Function.Injective i) (j : X →* G)
    (hj : ∀ a : Extension.plane 1 hn,j a.val=i (c.right a)) (hji : Function.Injective j) :
    A c i true=nativePlaneCore.map j := by
  rw [A,source_plane_graphCentralizer_eq_map c i hi j hj]
  exact (map_pCoreIn_of_injective 2 nativePlaneGraphCentralizer j hji).symm

/-- The model core as the actual subgroup of the first vertex. -/
def modelPlaneCoreInVertex : Subgroup V :=
  (TriangleLocal.localCore.map TriangleLocal.H.subtype).subgroupOf V

theorem nativePlaneCore_vertex_image :
    nativePlaneCore.map markedModelUnitaryExtensionEquivVertex.toMonoidHom=modelPlaneCoreInVertex := by
  apply map_injective (f:=(V).subtype) (V).subtype_injective
  rw [map_map]
  change nativePlaneCore.map markedModelVertexMap=_
  rw [nativePlaneCore_image,modelPlaneCoreInVertex,map_subgroupOf_eq_of_le]
  rintro _ ⟨a,ha,rfl⟩
  exact TriangleLocal.core_le_vertexLocal ha

theorem source_plane_core_model_image (hi : Function.Injective i) (j : X →* G)
    (hj : ∀ a : Extension.plane 1 hn,j a.val=i (c.right a)) (hji : Function.Injective j) :
    A c i true=modelPlaneCoreInVertex.map
      (j.comp markedModelUnitaryExtensionEquivVertex.symm.toMonoidHom) := by
  rw [←nativePlaneCore_vertex_image,map_map,source_plane_core_eq_map c i hi j hj hji]
  congr 1
  apply MonoidHom.ext
  intro a
  exact congrArg j (markedModelUnitaryExtensionEquivVertex.symm_apply_apply a).symm

/-- The independently marked second factor as a subgroup of the first vertex. -/
def modelComplementInVertex : Subgroup V :=
  (TriangleLocal.complementFactor.map TriangleLocal.H.subtype).subgroupOf V

theorem nativeLocalComplement_vertex_image :
    nativeLocalComplement.map markedModelUnitaryExtensionEquivVertex.toMonoidHom=modelComplementInVertex := by
  apply map_injective (f:=(V).subtype) (V).subtype_injective
  rw [map_map]
  change nativeLocalComplement.map markedModelVertexMap=_
  rw [nativeLocalComplement_image,modelComplementInVertex,map_subgroupOf_eq_of_le]
  rintro _ ⟨a,ha,rfl⟩
  exact TriangleLocal.complementFactor_le_vertexLocal ha

theorem source_complement_model_image (j : X →* G)
    (hj : ∀ a : Extension.plane 1 hn,j a.val=i (c.right a)) :
    sourceLocalComplement c i=modelComplementInVertex.map
      (j.comp markedModelUnitaryExtensionEquivVertex.symm.toMonoidHom) := by
  rw [←nativeLocalComplement_vertex_image]
  exact sourceLocalComplement_model_image c i j hj
end
end CFSG.Quasithin.ChapterF.Section05

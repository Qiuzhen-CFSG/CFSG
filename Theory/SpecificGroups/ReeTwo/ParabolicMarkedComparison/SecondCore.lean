module
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.Verified
public import Theory.SpecificGroups.ReeTwo.FirstParabolicCoordinates
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.CoreGeneration

/-!
# The marked second core in the full binary Ree group

The eight proved generators of the actual linear radical are images of
words in the coordinate subgroup C_S(Z₂(S)). Each word has zero root-three
coordinate. This gives containment of the actual core in the image; their
common order 2048 gives equality. Restriction preserves the already verified
Sylow map, so the marking is compatible with the first endpoint map.

Source: the verified Shinoda/Parrott root comparison and the eight-generator
core theorem for Aschbacher–Smith F.1.12, J.4.5 and J.4.7.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace ReeTwo.ParabolicMarkedComparison.Verified
open Tits.ExceptionalParabolics.FullRee
open Tits.ExceptionalParabolics.FullRee.LongRootPaths
open ReeF4 ReeF4.DerivedTits.Realization
open Tits.InvolutionRootGeometry.BinaryDerivedFusion

private def secondCoreWord (i : Fin 8) : SylowModel :=
  ![SylowModel.rootOne,SylowModel.rootOne*SylowModel.rootOne,SylowModel.root 4,
    SylowModel.rootOne*SylowModel.root 3,SylowModel.root 7,
    SylowModel.rootOne*SylowModel.root 2,SylowModel.root 6,
    SylowModel.root 1*SylowModel.rootOne⁻¹] i

private theorem secondCoreWord_mem (i : Fin 8) :
    secondCoreWord i∈SylowModel.firstParabolicCore := by
  rw [SylowModel.mem_firstParabolicCore_iff]
  exact (by decide +kernel : ∀i:Fin 8,(secondCoreWord i).left.b0=0) i

private theorem secondCoreWord_image (i : Fin 8) : sylowMap (secondCoreWord i)=coreGenerator i := by
  have hq : RootRelations.q=Ambient.rootOne := by
    apply toSplitGroup_injective 0
    rw [RootRelations.q,fixedU_matrix]
    simp only [Ambient.rootOne,Ambient.relative,toSplitGroup_apply]
  fin_cases i <;>
    simp [secondCoreWord,coreGenerator,hq,LongRootPaths.Atlas.a,Ambient.atlas_generator,
      Ambient.parrottWord,ParabolicMarkedComparison.sylowMap_root,
      ParabolicMarkedComparison.sylowMap_rootOne]

/-- The native intrinsic second core is the image of the very same Sylow
coordinate map already used on the first endpoint. -/
theorem secondCore_map : SylowModel.firstParabolicCore.map sylowMap = secondCore := by
  have hle : secondCore≤SylowModel.firstParabolicCore.map sylowMap := by
    rw [secondCore_eq_closure]
    apply (closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨secondCoreWord i,secondCoreWord_mem i,secondCoreWord_image i⟩
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective (sylowMap_injective RootVerification.relations),
    SylowModel.firstParabolicCore_card,secondCore,card_map_of_injective second.subtype_injective,
    second_core_card]

/-- The native second core isomorphism keeps the existing root/Sylow map. -/
def secondCoreEquiv : SylowModel.firstParabolicCore≃*secondCore :=
  (MonoidHom.ofInjective (f:=sylowMap.comp SylowModel.firstParabolicCore.subtype)
    ((sylowMap_injective RootVerification.relations).comp
    SylowModel.firstParabolicCore.subtype_injective)).trans
    (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp,range_subtype,secondCore_map]))

@[simp] theorem secondCoreEquiv_coe (a : SylowModel.firstParabolicCore) :
    (secondCoreEquiv a : Model 0)=sylowMap (a:SylowModel) := rfl

end ReeTwo.ParabolicMarkedComparison.Verified

module
public import CFSG.Quasithin.Chapter13.Section07.ComponentSeedMarked
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.SectionTransport
/-!
# Returning a prepared seed through its offender subgroup

The inclusion of the offender subgroup identifies the component commutator
spaces and their central quotients. The actual seed component equivalence
therefore returns unchanged to the original action.

Source: Aschbacher–Smith,13.7.18, printed p.945, applying B.5.1.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
open CFSG.Quasithin.ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
variable {A E B W : Type*} [Group A] [Finite A]
  [AddCommGroup E] [Module (ZMod 2) E]
  [Group B] [AddCommGroup W] [Module (ZMod 2) W]
/-- Return a literal prepared-seed action marking to the original component. -/
theorem centralSectionModel_of_subgroup_seed_mark
    (σ : Representation (ZMod 2) A E) (L N : Subgroup A) (hLN : L ≤ N)
    {D : Subgroup N} (hLA : ⁅L.subgroupOf N,D⁆ = L.subgroupOf N)
    (p : Prepared (σ.comp N.subtype) KnownSimple.IsKnownSimple hLA)
    (hL : IsComponent A L) (hi : IsIrrPlus σ L (moved σ L))
    (s : MovedSection (seedQuotientAction (σ.comp N.subtype) hLA)
      (seedComponentImage (σ.comp N.subtype) hLA))
    (τ : Representation (ZMod 2) B W)
    (em : ActionEquiv (s.action.comp (seedComponentImage (σ.comp N.subtype) hLA).subtype) τ) :
    HasCentralSectionModel σ L τ
      ((subgroupOfEquivOfLe hLN).symm.trans
        ((Preparation.seedComponentEquiv (σ.comp N.subtype) hLA p.component_faithful).trans
          em.groupEquiv)) := by
  have hI : (subspaceCommutator (σ.comp N.subtype) ⊤ (L.subgroupOf N)).map
      (LinearMap.id : E →ₗ[ZMod 2] E) = subspaceCommutator σ ⊤ L := by
    rw [Submodule.map_id,subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hLN]
  have hiN : IsIrrPlus (σ.comp N.subtype) (L.subgroupOf N)
      (moved (σ.comp N.subtype) (L.subgroupOf N)) := by
    change IsIrrPlus (σ.comp N.subtype) (L.subgroupOf N)
      (subspaceCommutator (σ.comp N.subtype) ⊤ (L.subgroupOf N))
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hLN]
    exact (IsIrrPlus.subgroupOf_iff σ L N hLN _).mpr hi
  exact centralSectionModel_transport (σ.comp N.subtype) σ (L.subgroupOf N) L
    (subgroupOfEquivOfLe hLN) LinearMap.id Function.injective_id hI (fun _ _ => rfl)
    τ _ (centralSectionModel_of_seed_mark (σ.comp N.subtype) hLA p (hL.subgroupOf hLN)
      hiN s τ em)
end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep

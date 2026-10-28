module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerG2CoreProduct
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.G2JoinFullActor
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Residual
public import Theory.Representation.G2BinaryPointGeneration

/-!
# The binary G₂ actor application

The intrinsic block actor covers the derived subgroup of the binary G₂ model.
The checked odd residual conjugate of the root eight therefore supplies the
literal two-conjugate generation premise: only the image of the root eight,
the model's root-eight image equality, and the sharp centralizer index remain
source inputs.  This module does not identify those inputs with a chosen
module or prove the index estimate.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A root-eight image in the full actor, together with the sharp index bound,
discharges the G₂ core elementarity and Frattini conclusion. -/
theorem g2Two_core_elementary_of_rootEight_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsG2TwoBlock L)
    (m : ChapterC.BlockModuleModel L ChapterC.g2TwoNaturalAction)
    (E : Subgroup ↥(L ⊔ (T : Subgroup G)))
    (himage : E.map (ChapterC.G2BlockAction.joinFullActor
      (D.sylow_normalizes_component) m) = Atlas.G2.BinaryCore.elementary)
    (hi : (centralizer ((E.map (L ⊔ (T : Subgroup G)).subtype : Subgroup G) : Set G)).relIndex
      ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤ 8) :
    IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      frattini ((L ⊔ (T : Subgroup G)).pCoreIn 2) = ⊥ := by
  let H := L ⊔ (T : Subgroup G)
  let q := ChapterC.G2BlockAction.joinFullActor D.sylow_normalizes_component m
  let A := E.map H.subtype
  obtain ⟨c, hc, hgen⟩ :=
    Atlas.G2.Natural.BinaryPointGeneration.exists_residual_conjugate_generating
  have hc' : c ∈ commutator (Atlas.G2.Model (ZMod 2)) := by
    rw [← Atlas.G2.EvenFieldFixedResidual.binary_twoResidual_eq_commutator]
    exact hc
  let g : ChapterC.G2BlockAction.Actor := ⟨c, hc'⟩
  have hgen' : commutator (Atlas.G2.Model (ZMod 2)) ≤
      E.map q ⊔ (E.map q).map (MulAut.conj g.val).toMonoidHom := by
    rw [himage]
    change commutator (Atlas.G2.Model (ZMod 2)) ≤
      Atlas.G2.BinaryCore.elementary ⊔
        Atlas.G2.BinaryCore.elementary.map (MulAut.conj c).toMonoidHom
    rw [hgen]
    exact le_top
  obtain ⟨k, hk⟩ := ChapterC.G2BlockAction.joinFullActor_two_conjugate_generation
    D.sylow_normalizes_component m E g hgen'
  exact g2Two_core_elementary_of_conjugate_index h D hfixed hescape hb A k.val k.property hk hi

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

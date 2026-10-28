module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.SourceGeometry
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.SourceMarking
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.MovingModule
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalF918
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalBorel

/-!
# The moving-actor branch of original 15.3.65

The original E.2 model supplies the exchanged geometry and the actual Borel
marking. F.9.16's placed quadratic actor lies in the Sylow image and acts
faithfully by conjugation on the residual. If it moves the selected component,
the whole-module calculation gives exactly the residual commutator inclusion
required by the seed contradiction, on the original local quotient action.

Source: Aschbacher–Smith 15.3.65, p.1152, using E.2.2 and D.3.7.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
open RepresentationReduction.SourceRestrictions.Cases.Exchanged
variable {G : Type*} [Group G] [Finite G]

/-- The moving-actor branch of original 15.3.65 on its literal local quotient. -/
theorem local_moving_fixedSpace_le {T : Sylow 2 G} {H M Y ZS Z : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (hH : H ∈ minimalSylowOutsideFamily T M)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.prop.1.2) ⊤)
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple H)
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z)
    (K : Subgroup H) (f : ℕ) (hmodel : OriginalBorel.OddModel T H M K f)
    (hn : ¬K.Normal) (B : Subgroup H)
    (hB : B ≤ (((Y ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H)
    (hA : IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hq : IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hd : fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤
      2 * rank (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hm : ¬ B.map (QuotientGroup.mk' (pCore 2 H)) ≤
      normalizer (actorImage H (K.map H.subtype) : Set (H ⧸ pCore 2 H))) :
    fixedSpace a.representation (borelImage H M) ≤
      fixedSpace a.representation (actorImage H (residual H)) := by
  have hgeo := local_geometry hH hP hSQTK K hmodel.component hmodel.quasisimple
    hmodel.generated hn
  let : IsSimpleGroup (actorImage H (K.map H.subtype)) :=
    local_component_simple hH hP hSQTK K hmodel.component hmodel.quasisimple
      hmodel.generated hn
  let : IsElementaryAbelian 2 (B.map (QuotientGroup.mk' (pCore 2 H))) := hA.2
  have hTK : actorImage H (T : Subgroup G) ≤
      normalizer (actorImage H (residual H) : Set (H ⧸ pCore 2 H)) := by
    have hr : actorImage H (residual H) = pResidual 2 (H ⧸ pCore 2 H) := by
      unfold actorImage residual subgroupOf
      rw [comap_map_eq_self_of_injective H.subtype_injective,map_pResidual_quotient]
    rw [hr,normalizer_eq_top]
    exact le_top
  have hs := hmodel.source_cases.resolve_left (fun h => hn h.1)
  exact moving_module_fixedSpace_le a.representation hgeo hTK a.faithful
    (actorImage_component_of_intrinsic H K hmodel.component hmodel.quasisimple)
    (source_internal_actor_le_sylow T hH.prop.1.2 B hB) hq
    (source_internal_actor_faithful_on_residual T hH.prop.1.2 B hB) hm hd
    (local_overlap_normalizer hs.2.1.kernel_eq hs.2.2.1)

/-- Restrict the moving-actor calculation to the residual commutator, as
required by the original seed contradiction. -/
theorem local_moving_commutator_borel_fixed {T : Sylow 2 G} {H M Y ZS Z : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (hH : H ∈ minimalSylowOutsideFamily T M)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.prop.1.2) ⊤)
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple H)
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z)
    (K : Subgroup H) (f : ℕ) (hmodel : OriginalBorel.OddModel T H M K f)
    (hn : ¬K.Normal) (B : Subgroup H)
    (hB : B ≤ (((Y ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H)
    (hA : IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hq : IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hd : fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤
      2 * rank (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hm : ¬ B.map (QuotientGroup.mk' (pCore 2 H)) ≤
      normalizer (actorImage H (K.map H.subtype) : Set (H ⧸ pCore 2 H))) :
    subspaceCommutator a.representation ⊤ (actorImage H (residual H)) ⊓
      fixedSpace a.representation (borelImage H M) ≤
      fixedSpace a.representation (actorImage H (residual H)) :=
  inf_le_right.trans (local_moving_fixedSpace_le hH hP hSQTK a K f hmodel hn B hB hA hq hd hm)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged

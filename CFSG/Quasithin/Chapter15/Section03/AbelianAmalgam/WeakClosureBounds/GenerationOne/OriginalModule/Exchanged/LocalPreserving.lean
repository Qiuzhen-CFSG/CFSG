module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.PreservingModule
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.SourceMarking
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalF918
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalBorel
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio.Comparisons

/-!
# The preserving-actor branch of original 15.3.65

The genuine exchanged E.2 model identifies the component and its Borel
on H/O₂(H). The placed F.9.16 actor is nontrivial, quadratic, and faithful
by conjugation on the residual. When it preserves the component, minimum
ratio selection and the irreducible Borel calculation force every Borel
fixed vector to be fixed by the residual. The original quotient maps and
field exponent are retained throughout.

Source: Aschbacher–Smith 15.3.65, printed p.1152, using E.2.2 and D.2.5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
open RepresentationReduction.SourceRestrictions.Cases.Exchanged
open RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
variable {G : Type*} [Group G] {H M : Subgroup G} {K : Subgroup H} {f : ℕ}

/-- The intrinsic exchanged model gives the central quotient model on the
literal action image, through the identity-on-representatives quotient map. -/
theorem local_source_model
    (hker : ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.sourceKernel
      (M.subgroupOf H) = pCore 2 H)
    (h : ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedModel
      (M.subgroupOf H) K f)
    (hZ : center (actorImage H (K.map H.subtype)) = ⊥) :
    SourceModel ((actorImage H (K.map H.subtype)) ⧸
      center (actorImage H (K.map H.subtype))) f := by
  have hm : SourceModel (BorelReduction.sourceImage H M (K.map H.subtype)) f := by
    rcases exchangedModel_of_intrinsic h with ⟨F,_,_,_,_,hF,e,_⟩ | ⟨m,hm,hf,e,_⟩
    · exact .linearTwo F hF e
    · exact .suzuki m hm hf e
  exact hm.transport ((centerQuotientEquiv hZ).trans (localComponentToSource hker))

universe u

variable {G : Type u} [Group G] [Finite G]

/-- The preserving-actor branch of original 15.3.65 on its literal local quotient. -/
theorem local_preserving_fixedSpace_le {T : Sylow 2 G} {H M Y ZS Z : Subgroup G}
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
    (hp : B.map (QuotientGroup.mk' (pCore 2 H)) ≤
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
  have hK := actorImage_component_of_intrinsic H K hmodel.component hmodel.quasisimple
  let : IsQuasisimple (actorImage H (K.map H.subtype)) := hK.2
  have hZ : center (actorImage H (K.map H.subtype)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (center (actorImage H (K.map H.subtype))) inferInstance with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim
  exact preserving_module_fixedSpace_le a.representation hgeo hTK
    (RepresentationReduction.actorImage_residual_sup_sylow T hH.prop.1.2)
    (ChapterE.Structure.sqtk_two_quotient hSQTK (pCore 2 H) pCore_isPGroup)
    a.faithful hK (source_internal_actor_le_sylow T hH.prop.1.2 B hB) hA hq
    (source_internal_actor_faithful_on_residual T hH.prop.1.2 B hB) hp hd
    (local_source_model hs.2.1.kernel_eq hs.2.2.1 hZ)
    hmodel.exponent_gt_one hmodel.exponent_odd
    (local_overlap_normalizer hs.2.1.kernel_eq hs.2.2.1)

/-- Restrict the preserving-actor calculation to the residual commutator, as
required by the original seed contradiction. -/
theorem local_preserving_commutator_borel_fixed {T : Sylow 2 G} {H M Y ZS Z : Subgroup G}
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
    (hp : B.map (QuotientGroup.mk' (pCore 2 H)) ≤
      normalizer (actorImage H (K.map H.subtype) : Set (H ⧸ pCore 2 H))) :
    subspaceCommutator a.representation ⊤ (actorImage H (residual H)) ⊓
      fixedSpace a.representation (borelImage H M) ≤
      fixedSpace a.representation (actorImage H (residual H)) :=
  inf_le_right.trans (local_preserving_fixedSpace_le hH hP hSQTK a K f hmodel hn B hB hA hq hd hp)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged

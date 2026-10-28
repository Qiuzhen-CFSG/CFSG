module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Normal.QuadraticModules
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Normal.Markings
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalBorel.NormalActor
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalF918

/-!
# The normal-component calculation for the original 15.3.65 action

The intrinsic normal component has a one-element Sylow conjugacy orbit, so
its image is the entire two-residual image in H/O₂(H). The genuine E.2 odd-field
marking and the three-prime overlap collapse the source central kernel. Its
Borel is a Sylow normalizer on the same component, with the original quotient
maps retained.

F.9.18(2) makes the placed F.9.16 quadratic actor faithful on this component.
The proved quadratic composition-factor argument therefore sends every vector
fixed by the original Borel into the residual fixed space. This gives exactly
the commutator/fixed-space intersection required by the original seed argument.

Source: Aschbacher–Smith, 15.3.65, printed p.1152; E.2.2, pp.215–216;
F.9.16(3) and F.9.18(2), pp.324–326. No classification callback, seed-fixation
hypothesis, or equality of the generation parameter and field exponent is used.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
variable {G : Type*} [Group G] [Finite G]

/-- Normality of the intrinsic component collapses its Sylow orbit before
passing to the literal two-core quotient. -/
theorem original_residual_eq_component {H M : Subgroup G} {T : Sylow 2 G}
    (hTH : (T : Subgroup G) ≤ H) {K : Subgroup H} {f : ℕ}
    (model : OriginalBorel.OddModel T H M K f) (hn : K.Normal) :
    residual H = K.map H.subtype := by
  let := hn
  have hc : conjugateSpanBy K ((T : Subgroup G).subgroupOf H) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl le_normalizer_of_normal) (le_conjugateSpanBy _ _)
  have hm := congrArg (fun L : Subgroup H => L.map H.subtype) hc
  rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hTH] at hm
  exact model.residual_eq.trans hm

/-- The original normal-component calculation, on the exact action H/O₂(H)
on the span quotient. Its common quadratic actor is the original placed
F.9.16 subgroup, and its Borel is the original image of M∩O²(H). -/
theorem original_borel_calculation
    {H M ZS Z Y : Subgroup G} {T : Sylow 2 G}
    (hTH : (T : Subgroup G) ≤ H)
    (_hP : ChapterB.IsMinimalParabolicOver (T.subtype hTH) ⊤)
    (_hSQTK : IsSQTK KnownSimple.IsKnownSimple H)
    [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z)
    {K : Subgroup H} {f : ℕ} (model : OriginalBorel.OddModel T H M K f)
    (hn : K.Normal) (hthree : ¬3 ∣ Nat.card (M ⊓ H : Subgroup G))
    (B : Subgroup H)
    (hB : B ≤ (((Y ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H)
    (hA : IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hq : IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hc : fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤
      2 * rank (B.map (QuotientGroup.mk' (pCore 2 H)))) :
    subspaceCommutator a.representation ⊤ (actorImage H (residual H)) ⊓
      fixedSpace a.representation (borelImage H M) ≤
        fixedSpace a.representation (actorImage H (residual H)) := by
  let := hn
  let L : Subgroup (H ⧸ pCore 2 H) := MarkedModels.actorImage K
  let A := B.map (QuotientGroup.mk' (pCore 2 H))
  let C : Subgroup L := (MarkedModels.actorImage (M.subgroupOf H ⊓ K)).subgroupOf L
  let : L.Normal := hn.map _ (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple L := OriginalBorel.NormalActor.actor_quasisimple
    (model.normal_input hn hthree)
  have hZ : center L = ⊥ := (model.normal_actor_center hn hthree).1
  have hs : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) :=
    (IsSQTK.equiv (QuotientGroup.quotientMulEquivOfEq
      (model.normal_actor_center hn hthree).2)).mp model.quotient_sqtk
  have hres := original_residual_eq_component hTH model hn
  have hL : actorImage H (residual H) = L := by rw [hres,actorImage_internal]; rfl
  have hborel : borelImage H M = MarkedModels.actorImage (M.subgroupOf H ⊓ K) := by
    change ((M ⊓ residual H).subgroupOf H).map _ = _
    rw [hres]
    change ((M ⊓ K.map H.subtype).comap H.subtype).map _ = _
    rw [comap_inf,comap_map_eq_self_of_injective H.subtype_injective]
    rfl
  let e : L ≃* MarkedModels.sourceImage (M.subgroupOf H) K := model.normal_componentEquiv hn hthree
  have he : C.map e.toMonoidHom = MarkedModels.componentOverlap (M.subgroupOf H) K :=
    model.normal_componentEquiv_overlap hn hthree
  have hm : SourceModel (L ⧸ center L) f :=
    (source_model_of_normal_cases (model.normal_cases hn).2).transport
      ((centerQuotientEquiv hZ).trans e)
  have hC : ∃ P : Sylow 2 L, normalizer (P : Set L) = C :=
    exists_sylow_normalizer_of_equiv e C _ he
      (source_borel_normalizer_of_normal_cases (model.normal_cases hn).2 model.exponent_gt_one)
  have hAC : A ⊓ centralizer (L : Set (H ⧸ pCore 2 H)) = ⊥ := by
    rw [← hL]
    exact source_internal_actor_faithful_on_residual T hTH B hB
  have hfix := fixedSpace_le_of_quadratic_actor a.representation L A hZ hs
    hA hq hc hAC hm model.exponent_gt_one model.exponent_odd C hC
  intro v hv l
  have hvC : v ∈ fixedSpace (a.representation.comp L.subtype) C := by
    intro c
    exact hv.2 ⟨c.val.val,hborel ▸ c.property⟩
  have hl : (l : H ⧸ pCore 2 H) ∈ L := hL ▸ l.property
  exact hfix hvC ⟨⟨l,hl⟩,mem_top _⟩
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal

module
public import Theory.Representation.BinaryOffender.SylowFixedGeneration
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.LocalInputs
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.Terminal
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.PrimeCoreAction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.Setup
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# Original quotient and actor reductions for 15.3.65

The actual seed generates U/Z under H/O₂(H), so the Sylow-fixed generation
lemma proves the central supplement required by B.2.14. An actor placed in the
edge two-core is faithful on the residual image because that image is normal,
supplemented by the edge, and the ambient two-core quotient has trivial two-core.
The intrinsic C-component and its quasisimple two-core quotient give an ordinary
component of this exact actor. Its residual orbit is transported by the same maps.

These facts give F.9.18(2), (3), and (6) on the original representation and actor.
The Sylow orbit of a residual Irr⁺ section is already the full H-orbit. The
specialized marked-model calculation in F.9.18(4--5), B.4, and B.5 remains separate;
the final theorem consumes its explicit Borel fixed-space inclusion and derives
the source contradiction without assuming a decomposition or seed fixation.

Source: Aschbacher--Smith, F.9.18, printed pp.325--326, and 15.3.65, p.1152
(combined manuscript, 1 March 2004).
-/


@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G]

/-- The literal image of the seed generates the original quotient representation. -/
theorem seedSpace_iSup_maps_eq_top
    {H ZS Z : Subgroup G} [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z) :
    (⨆ g : H ⧸ pCore 2 H, (seedSpace a ZS).map (a.representation g)) = ⊤ := by
  let U := conjugateSpanBy ZS H
  let J := ⨆ g : H ⧸ pCore 2 H, (seedSpace a ZS).map (a.representation g)
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let C : Subgroup U := (Subgroup.toAddSubgroup.symm J.toAddSubgroup).comap q
  let B : Subgroup G := C.map U.subtype
  have hUB : U ≤ B := by
    apply (closure_le _).mpr
    rintro x ⟨h, hh, z, hz, rfl⟩
    let zU : U := ⟨z, le_conjugateSpanBy ZS H hz⟩
    let hH : H := ⟨h, hh⟩
    let w : U := ⟨h * z * h⁻¹, le_normalizer_iff.mp a.normalizes h hh z zU.property⟩
    refine ⟨w, ?_, rfl⟩
    change Additive.ofMul (q w) ∈ J
    have hs : Additive.ofMul (q zU) ∈ seedSpace a ZS :=
      Submodule.subset_span ⟨zU, hz, rfl⟩
    have hm := le_iSup_maps a.representation (seedSpace a ZS) hs
    have hi := (iSup_maps_invariant a.representation (seedSpace a ZS)
      (mem_top (QuotientGroup.mk' (pCore 2 H) hH)) _).2 hm
    rw [a.conjugation] at hi
    exact hi
  apply top_unique
  intro v _
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) v.toMul
  obtain ⟨w, hw, he⟩ := hUB u.property
  have he' : w = u := Subtype.ext he
  subst w
  change Additive.ofMul (q u) ∈ J at hw
  have he : Additive.ofMul (q u) = v := congrArg Additive.ofMul hu
  exact he ▸ hw

/-- B.2.14's central supplement on the actual U/Z, with the two-residual
actor and Sylow action retained literally. -/
theorem source_span_decomposition [Finite G]
    {H ZS Z : Subgroup G} [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z)
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (hT : seedSpace a ZS ≤ fixedSpace a.representation (actorImage H T)) :
    subspaceCommutator a.representation ⊤ (actorImage H (residual H)) ⊔
      fixedSpace a.representation ⊤ = ⊤ := by
  let f := QuotientGroup.mk' (pCore 2 H)
  let P := (T.subtype hTH).mapSurjective (f := f) (QuotientGroup.mk'_surjective _)
  have hP : (P : Subgroup (H ⧸ pCore 2 H)) = actorImage H T := rfl
  have hR : ((residual H).subgroupOf H).Normal := by
    change (((pResidual 2 H).map H.subtype).comap H.subtype).Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  let := hR
  let : (actorImage H (residual H)).Normal :=
    hR.map _ (QuotientGroup.mk'_surjective _)
  apply moved_sup_fixedSpace_of_sylow_fixed_generators a.representation
    (actorImage H (residual H)) P _ (seedSpace a ZS) _ (seedSpace_iSup_maps_eq_top a)
  · rw [hP]
    exact RepresentationReduction.actorImage_residual_sup_sylow T hTH
  · rwa [hP]

/-- Source 15.3.65's terminal contradiction after the actual F.9.18/B.4/B.5
calculation on the commutator space. The former B.2.14 premise is discharged. -/
theorem false_of_commutator_borel_calculation [Finite G]
    {H ZS Z M V K : Subgroup G} [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hZV : ZS ≤ V) (hres : residual (M ⊓ H) ≤ centralizer (V : Set G))
    (hT : seedSpace a ZS ≤ fixedSpace a.representation (actorImage H T))
    (hZZS : Z ≤ ZS) (hHZ : H ≤ centralizer (Z : Set G))
    (hK : (K.subgroupOf H).IsCComponent)
    (horbit : residual H = conjugateSpanBy K T)
    (hcalc : subspaceCommutator a.representation ⊤ (actorImage H (residual H)) ⊓
      fixedSpace a.representation (borelImage H M) ≤
        fixedSpace a.representation (actorImage H (residual H))) : False := by
  exact not_seedSpace_le_fixedSpace_of_component a rfl hZZS hHZ hK horbit
    (RepresentationReduction.seedSpace_le_fixedSpace_of_local_inputs
      a T hTM hTH (le_conjugateSpanBy ZS H) hZV hres hT
      (source_span_decomposition a T hTH hT) hcalc)
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three
open CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical.Offenders
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- The edge two-core has faithful conjugation action on the actual residual
image. The edge only needs to contain the given Sylow subgroup. -/
theorem edgeCore_faithful_on_residual (H J : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) (hTJ : (T : Subgroup G) ≤ J) :
    actorImage H (J.pCoreIn 2) ⊓
      centralizer (actorImage H (residual H) : Set (H ⧸ pCore 2 H)) = ⊥ := by
  have hR : ((residual H).subgroupOf H).Normal := by
    change (((pResidual 2 H).map H.subtype).comap H.subtype).Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  let : (actorImage H (residual H)).Normal :=
    hR.map _ (QuotientGroup.mk'_surjective _)
  have hgen : actorImage H (residual H) ⊔ actorImage H J = ⊤ := by
    apply top_unique
    rw [← RepresentationReduction.actorImage_residual_sup_sylow T hTH]
    exact sup_le_sup_left (map_mono (subgroupOf_mono H hTJ)) _
  exact centralizer_inf_eq_bot_of_supplement _ _ _ hgen
    (starImage_isPGroup H _ (isPGroup_pCoreIn 2 J))
    (starImage_normalizes H (le_normalizer_pCoreIn 2 J)) (hstar_twoCore H)

/-- F.9.18(2) on the same actual subgroup supplied by F.9.16(3), preserving
its literal image in H/O₂(H). -/
theorem placed_actor_faithful_on_residual {H J B : Subgroup G} (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) (hTJ : (T : Subgroup G) ≤ J)
    (hB : B ≤ J.pCoreIn 2) :
    actorImage H B ⊓
      centralizer (actorImage H (residual H) : Set (H ⧸ pCore 2 H)) = ⊥ := by
  apply bot_unique
  exact (inf_le_inf_right _ (map_mono (subgroupOf_mono H hB))).trans_eq
    (edgeCore_faithful_on_residual H J T hTH hTJ)

/-- The original edge is (Y T)∩H; its Sylow containment is automatic. -/
theorem source_actor_faithful_on_residual {H Y B : Subgroup G} (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H)
    (hB : B ≤ ((Y ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2) :
    actorImage H B ⊓
      centralizer (actorImage H (residual H) : Set (H ⧸ pCore 2 H)) = ⊥ :=
  placed_actor_faithful_on_residual T hTH (le_inf le_sup_right hTH) hB
/-- The internal subgroup form matches the actor returned by the original
F.9.16 construction, with exactly the same quotient homomorphism. -/
theorem source_internal_actor_faithful_on_residual {H Y : Subgroup G}
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H) (B : Subgroup H)
    (hB : B ≤ (((Y ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H) :
    B.map (QuotientGroup.mk' (pCore 2 H)) ⊓
      centralizer (actorImage H (residual H) : Set (H ⧸ pCore 2 H)) = ⊥ := by
  have hb : B.map H.subtype ≤ ((Y ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2 := by
    rintro x ⟨b, hb, rfl⟩
    exact hB hb
  have hf := source_actor_faithful_on_residual T hTH hb
  unfold actorImage at hf
  rw [show (B.map H.subtype).subgroupOf H = B from
    comap_map_eq_self_of_injective H.subtype_injective B] at hf
  exact hf

/-- F.9.18(6)'s actual section alternative after the edge placement has
supplied faithfulness of the common actor. The component and orbit inputs
come from the independent E.2 source reduction. -/
theorem source_section_alternatives
    {H Y ZS Z : Subgroup G} [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z)
    (W : Subrepresentation a.representation) (K : Subgroup G)
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H) (B : Subgroup H)
    (hB : B ≤ (((Y ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H)
    (hK : Theory.GroupTheory.IsComponent (H ⧸ pCore 2 H) (actorImage H K))
    (horbit : conjugateSpanBy (actorImage H K) (actorImage H T) =
      actorImage H (residual H))
    (hA : IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
      IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
      actionRatio a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤ 2)
    (hW : W.toSubmodule ≠ ⊥)
    (hc : subspaceCommutator a.representation W.toSubmodule
      (actorImage H (residual H)) = W.toSubmodule) :
    W.toSubmodule = subspaceCommutator a.representation ⊤ (actorImage H (residual H)) ∨
    (IsFFModule (imageRepresentation W.toRepresentation) ∧
      IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
      IsStrongFFModule (imageRepresentation W.toRepresentation) ∨
        IsStrongFFModule (imageRepresentation W.quotientRepresentation) :=
  RepresentationReduction.SourceRestrictions.local_section_alternatives a W K T
    (B.map (QuotientGroup.mk' (pCore 2 H))) hK horbit hA
    (source_internal_actor_faithful_on_residual T hTH B hB) hW hc

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G]

/-- The component selected inside H has its literal image in H/O₂(H). -/
theorem actorImage_internal (H : Subgroup G) (K : Subgroup H) :
    actorImage H (K.map H.subtype) = K.map (QuotientGroup.mk' (pCore 2 H)) := by
  unfold actorImage subgroupOf
  rw [comap_map_eq_self_of_injective H.subtype_injective]

/-- Intrinsic quasisimplicity modulo O₂ gives an ordinary component of the
actual actor quotient. -/
theorem actorImage_component_of_intrinsic [Finite G] (H : Subgroup G) (K : Subgroup H)
    (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    IsComponent (H ⧸ pCore 2 H) (actorImage H (K.map H.subtype)) := by
  rw [actorImage_internal]
  let : IsQuasisimple (K ⧸ pCore 2 K) := hq
  let q := QuotientGroup.mk' (pCore 2 H)
  have hsub : (K.map q).IsSubnormal := hK.subnormal.map (QuotientGroup.mk'_surjective _)
  have hquasi : IsQuasisimple (K.map q) :=
    IsQuasisimple.of_mulEquiv (hK.subnormal.quotientCoreImageEquiv 2)
  exact ⟨hsub, hquasi⟩

/-- The source residual orbit transports through both the ambient inclusion
and the two-core quotient, retaining the selected intrinsic component. -/
theorem actorImage_orbit_of_intrinsic (H : Subgroup G) (K : Subgroup H)
    (T : Subgroup G) (hTH : T ≤ H)
    (hres : residual H = conjugateSpanBy (K.map H.subtype) T) :
    conjugateSpanBy (actorImage H (K.map H.subtype)) (actorImage H T) =
      actorImage H (residual H) := by
  let Ti : Subgroup H := T.subgroupOf H
  have hmap : (conjugateSpanBy K Ti).map H.subtype =
      conjugateSpanBy (K.map H.subtype) T := by
    rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le hTH]
  have hle : conjugateSpanBy (K.map H.subtype) T ≤ H := hres ▸ residual_le H
  have hint : (conjugateSpanBy (K.map H.subtype) T).subgroupOf H =
      conjugateSpanBy K Ti := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hle, hmap]
  rw [hres, actorImage_internal, actorImage, actorImage, hint]
  change conjugateSpanBy (K.map (QuotientGroup.mk' (pCore 2 H)))
    (Ti.map (QuotientGroup.mk' (pCore 2 H))) =
    (conjugateSpanBy K Ti).map (QuotientGroup.mk' (pCore 2 H))
  exact (map_conjugateSpanBy K Ti _).symm

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne
open Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The placed edge actor lies in the original Sylow subgroup. -/
theorem source_internal_actor_le_sylow {H Y : Subgroup G}
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H) (B : Subgroup H)
    (hB : B ≤ (((Y ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H) :
    B.map (QuotientGroup.mk' (pCore 2 H)) ≤ actorImage H T := by
  have hT : (T : Subgroup G) ≤ (Y ⊔ (T : Subgroup G)) ⊓ H :=
    le_inf le_sup_right hTH
  have hcore : ((Y ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2 ≤ T :=
    (isPGroup_pCoreIn 2 _).le_sylow_of_normalized T
      (hT.trans (le_normalizer_pCoreIn 2 _))
  exact map_mono (hB.trans (subgroupOf_mono H hcore))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- In the original minimal-parabolic setting K₀T=H. Thus the T-orbit of
an Irr⁺ residual section already is its H-orbit; the orbit-growth cases
of D.3.10 and D.3.21 do not enter this specialization. -/
theorem source_section_sylow_orbit_eq_full
    {H ZS Z : Subgroup G} [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z)
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (I : Submodule (ZMod 2) (Additive ((conjugateSpanBy ZS H) ⧸
      Z.subgroupOf (conjugateSpanBy ZS H))))
    (hI : IsIrrPlusWith a.representation (actorImage H (residual H)) (actorImage H T) I) :
    orbitSpan a.representation (actorImage H T) I = orbitSpan a.representation ⊤ I := by
  have hs : (⊤ : Subgroup (H ⧸ pCore 2 H)) ≤
      subspaceStabilizer a.representation (orbitSpan a.representation (actorImage H T) I) := by
    rw [← RepresentationReduction.actorImage_residual_sup_sylow T hTH]
    exact sup_le (orbitSpan_component_invariant a.representation hI.normalizes hI.isIrrPlus)
      (orbitSpan_invariant a.representation (actorImage H T) I)
  apply le_antisymm
  · exact orbitSpan_le a.representation (le_orbitSpan a.representation ⊤ I)
      (le_top.trans (orbitSpan_invariant a.representation ⊤ I))
  · exact orbitSpan_le a.representation (le_orbitSpan a.representation (actorImage H T) I) hs

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- F.9.18(6) with the intrinsic component selected by the genuine E.2
reduction and the same internally placed F.9.16 actor. -/
theorem source_section_alternatives_of_intrinsic
    {H Y ZS Z : Subgroup G} [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z)
    (W : Subrepresentation a.representation) (K : Subgroup H)
    (hK : K.IsCComponent) (hquasi : IsQuasisimple (K ⧸ pCore 2 K))
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (horbit : residual H = conjugateSpanBy (K.map H.subtype) T)
    (B : Subgroup H)
    (hB : B ≤ (((Y ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H)
    (hA : IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hq : IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hb : fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤
      2 * rank (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hW : W.toSubmodule ≠ ⊥)
    (hc : subspaceCommutator a.representation W.toSubmodule
      (actorImage H (residual H)) = W.toSubmodule) :
    W.toSubmodule = subspaceCommutator a.representation ⊤ (actorImage H (residual H)) ∨
    (IsFFModule (imageRepresentation W.toRepresentation) ∧
      IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
      IsStrongFFModule (imageRepresentation W.toRepresentation) ∨
        IsStrongFFModule (imageRepresentation W.quotientRepresentation) :=
  source_section_alternatives a W (K.map H.subtype) T hTH B hB
    (actorImage_component_of_intrinsic H K hK hquasi)
    (actorImage_orbit_of_intrinsic H K T hTH horbit)
    ⟨hA, hq, (RepresentationReduction.SourceRestrictions.actionRatio_le_two_iff
      a.representation hA).mpr hb⟩ hW hc

/-- The remaining commutator-space calculation feeds the terminal source
contradiction for the same intrinsic E.2 component. -/
theorem false_of_intrinsic_commutator_borel_calculation
    {H ZS Z M V : Subgroup G} [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z)
    (K : Subgroup H) (hK : K.IsCComponent)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hZV : ZS ≤ V) (hres : residual (M ⊓ H) ≤ centralizer (V : Set G))
    (hT : seedSpace a ZS ≤ fixedSpace a.representation (actorImage H T))
    (hZZS : Z ≤ ZS) (hHZ : H ≤ centralizer (Z : Set G))
    (horbit : residual H = conjugateSpanBy (K.map H.subtype) T)
    (hcalc : subspaceCommutator a.representation ⊤ (actorImage H (residual H)) ⊓
      fixedSpace a.representation (borelImage H M) ≤
        fixedSpace a.representation (actorImage H (residual H))) : False := by
  apply false_of_commutator_borel_calculation a T hTM hTH hZV hres hT hZZS hHZ
    (K := K.map H.subtype) _ horbit hcalc
  simpa only [subgroupOf, comap_map_eq_self_of_injective H.subtype_injective] using hK

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne
open RepresentationReduction.SourceRestrictions
variable {G : Type*} [Group G] [Finite G]

/-- F.9.18(3) on a nonzero full-commutator subrepresentation: the original
placed actor remains faithful and quadratic on the literal action image. -/
theorem source_section_quadratic_bound
    {H Y ZS Z : Subgroup G} [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z)
    (W : Subrepresentation a.representation) (K : Subgroup H)
    (hK : K.IsCComponent) (hquasi : IsQuasisimple (K ⧸ pCore 2 K))
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (horbit : residual H = conjugateSpanBy (K.map H.subtype) T)
    (B : Subgroup H)
    (hB : B ≤ (((Y ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H)
    (hA : IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hq : IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hb : fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤
      2 * rank (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hW : W.toSubmodule ≠ ⊥)
    (hc : subspaceCommutator a.representation W.toSubmodule
      (actorImage H (residual H)) = W.toSubmodule) :
    (∀ b ∈ B.map (QuotientGroup.mk' (pCore 2 H)),
      (∀ w, W.toRepresentation b w = w) → b = 1) ∧
      quadraticRatio (imageRepresentation W.toRepresentation) ≤ 2 := by
  let A := B.map (QuotientGroup.mk' (pCore 2 H))
  have ho := actorImage_orbit_of_intrinsic H K T hTH horbit
  have hn := subrepresentation_action_nontrivial a.representation W _ hW hc
  have hker := action_kernel_le_centralizer_of_component_orbit W.toRepresentation
    (actorImage H (K.map H.subtype)) (actorImage H T)
    (actorImage_component_of_intrinsic H K hK hquasi) (by simpa only [ho] using hn)
  rw [ho] at hker
  have hf := source_internal_actor_faithful_on_residual T hTH B hB
  have hfaith : ∀ b ∈ A, (∀ w, W.toRepresentation b w = w) → b = 1 := by
    intro b hb hw
    exact mem_bot.mp (hf ▸ (show b ∈ A ⊓ centralizer (actorImage H (residual H) : Set _) from
      ⟨hb, hker ((actionHom_eq_one_iff W.toRepresentation b).mpr hw)⟩))
  refine ⟨hfaith, (quadraticRatio_le_two_iff _).mpr ?_⟩
  refine ⟨actionSubgroup W.toRepresentation A, hA.actionSubgroup _ hfaith, ?_, ?_⟩
  · rintro x ⟨b, hb, rfl⟩ y ⟨c, hc, rfl⟩ v
    exact quadratic_subrepresentation a.representation W hq b hb c hc v
  · rw [fixedCodim_actionSubgroup, actionSubgroup_rank W.toRepresentation A hfaith]
    exact (fixedCodim_subrepresentation_le a.representation W A).trans hb

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne
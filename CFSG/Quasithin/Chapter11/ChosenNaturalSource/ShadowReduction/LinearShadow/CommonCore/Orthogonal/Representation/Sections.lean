module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Representation.Assembly

/-!
# The literal natural sections of the common core

The original flag's affine projection of L₂ has kernel V₂. Its linear part
has kernel P, and its translations identify P/V₂ with the natural plane.
The original V₂ marking intertwines the same linear projection, proving
that both literal sections have the same natural L₂-action. No comparison
with the independent K-field is assumed.

Source: Aschbacher--Smith, printed p.774, final paragraph. The printed
sections V and P/V are corrected here to V₂ and P/V₂, since P ∩ V = V₂.
The common-core orthogonal owner retains component recognition and assembly.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)
include d

def source_localAffineProjection : f.Li 1 →* Matrix.SL2.Affine S.field.Carrier :=
  ((Matrix.PSL3.LinearThree.lineLocalAffineEquiv S.field.Carrier).toMonoidHom.comp
    (SL3.PlaneAction.localProjection D S m 1)).comp
    (MulEquiv.subgroupCongr (congrArg (fun a : InvariantFlag (.sl3 m) => a.Li 1)
      (source_flag_eq d))).toMonoidHom

theorem source_localAffineProjection_surjective :
    Function.Surjective (source_localAffineProjection d) :=
  ((Matrix.PSL3.LinearThree.lineLocalAffineEquiv S.field.Carrier).surjective.comp
    (SL3.PlaneAction.localProjection_surjective D S m 1)).comp (MulEquiv.surjective _)

def source_sectionActors : f.Li 1 →* SL(2,S.field.Carrier) :=
  SemidirectProduct.rightHom.comp (source_localAffineProjection d)

theorem source_sectionActors_surjective : Function.Surjective (source_sectionActors d) :=
  SemidirectProduct.rightHom_surjective.comp (source_localAffineProjection_surjective d)

theorem source_sectionActors_ker :
    (source_sectionActors d).ker = (pairCore V H h).subgroupOf (f.Li 1) := by
  let e := MulEquiv.subgroupCongr
    (congrArg (fun a : InvariantFlag (.sl3 m) => a.Li 1) (source_flag_eq d))
  have he : source_sectionActors d = (SL3.PlaneAction.planeProjection D S m).comp e.toMonoidHom := rfl
  rw [he,← MonoidHom.comap_ker,SL3.PlaneAction.planeProjection_ker]
  ext l
  change e l ∈ pCore 2 ((SL3.flag D S m).Li 1) ↔ (l : G) ∈ pairCore V H h
  have hc : ((SL3.flag D S m).Li 1).pCoreIn 2 = pairCore V H h := by
    rw [← source_flag_eq d]
    exact d.local_core
  rw [← hc]
  exact (mem_map_iff_mem (f := ((SL3.flag D S m).Li 1).subtype)
    ((SL3.flag D S m).Li 1).subtype_injective).symm

theorem source_localAffineProjection_ker :
    (source_localAffineProjection d).ker = (f.Vi 1).subgroupOf (f.Li 1) := by
  ext l
  let l' : (SL3.flag D S m).Li 1 :=
    (MulEquiv.subgroupCongr
      (congrArg (fun a : InvariantFlag (.sl3 m) => a.Li 1) (source_flag_eq d))) l
  have hl : (l' : G) = (l : G) := rfl
  change Matrix.PSL3.LinearThree.lineLocalAffineEquiv S.field.Carrier
    (SL3.PlaneAction.localProjection D S m 1 l') = 1 ↔ (l : G) ∈ f.Vi 1
  rw [map_eq_one_iff _ (Matrix.PSL3.LinearThree.lineLocalAffineEquiv S.field.Carrier).injective]
  have he : SL3.PlaneAction.localProjection D S m 1 l' = 1 ↔ (l : G) ∈ V := by
    rw [← Subtype.coe_inj,SL3.PlaneAction.localProjection_coe]
    change SL3.PlaneAction.alignedQuotient D S m
      ⟨l',(localResidual_le _ l'.property).1⟩ = 1 ↔ _
    rw [← MonoidHom.mem_ker,SL3.PlaneAction.alignedQuotient_ker]
    have hi := (mem_map_iff_mem (f := L.subtype) (K := pCore 2 L)
      (x := (⟨l',(localResidual_le _ l'.property).1⟩ : L)) L.subtype_injective).symm
    change _ ↔ (l : G) ∈ L.pCoreIn 2 at hi
    simpa only [d.seed_core] using hi
  rw [he,← d.intersection_eq_plane]
  constructor
  · intro hv
    have hq : source_localAffineProjection d l = 1 := by
      change Matrix.PSL3.LinearThree.lineLocalAffineEquiv S.field.Carrier
        (SL3.PlaneAction.localProjection D S m 1 l') = 1
      rw [(he.mpr hv),map_one]
    have hp : l ∈ (source_sectionActors d).ker := by
      change SemidirectProduct.rightHom (source_localAffineProjection d l) = 1
      rw [hq,map_one]
    rw [source_sectionActors_ker] at hp
    exact ⟨hp,hv⟩
  · exact And.right

def source_coreTranslations : pairCore V H h →* Matrix.SL2.translations S.field.Carrier :=
  ((source_localAffineProjection d).comp
    (inclusion (source_pairCore_le_factors d).2)).codRestrict _ (by
      intro p
      change source_sectionActors d (inclusion (source_pairCore_le_factors d).2 p) = 1
      apply MonoidHom.mem_ker.mp
      rw [source_sectionActors_ker]
      exact p.property)

def source_quotientPlaneProjection :
    pairCore V H h →* Multiplicative (Fin 2 → S.field.Carrier) :=
  (Matrix.SL2.translationsEquiv S.field.Carrier).symm.toMonoidHom.comp
    (source_coreTranslations d)

theorem source_quotientPlaneProjection_inl (p : pairCore V H h) :
    SemidirectProduct.inl (source_quotientPlaneProjection d p) =
      source_localAffineProjection d (inclusion (source_pairCore_le_factors d).2 p) := by
  exact congrArg Subtype.val
    ((Matrix.SL2.translationsEquiv S.field.Carrier).apply_symm_apply (source_coreTranslations d p))

theorem source_quotientPlaneProjection_surjective :
    Function.Surjective (source_quotientPlaneProjection d) := by
  intro v
  obtain ⟨l,hl⟩ := source_localAffineProjection_surjective d (SemidirectProduct.inl v)
  have hp : (l : G) ∈ pairCore V H h := by
    have hk : l ∈ (source_sectionActors d).ker := by
      change SemidirectProduct.rightHom (source_localAffineProjection d l) = 1
      rw [hl,SemidirectProduct.rightHom_inl]
    rw [source_sectionActors_ker] at hk
    exact hk
  refine ⟨⟨l,hp⟩,(SemidirectProduct.inl_injective (φ := Matrix.SL2.naturalAction S.field.Carrier)) ?_⟩
  rw [source_quotientPlaneProjection_inl]
  exact hl

theorem source_quotientPlaneProjection_ker :
    (source_quotientPlaneProjection d).ker = (f.Vi 1).subgroupOf (pairCore V H h) := by
  ext p
  change source_quotientPlaneProjection d p = 1 ↔ (p : G) ∈ f.Vi 1
  rw [← map_eq_one_iff (SemidirectProduct.inl :
    Multiplicative (Fin 2 → S.field.Carrier) →* Matrix.SL2.Affine S.field.Carrier)
      SemidirectProduct.inl_injective,source_quotientPlaneProjection_inl]
  change inclusion (source_pairCore_le_factors d).2 p ∈
    (source_localAffineProjection d).ker ↔ _
  rw [source_localAffineProjection_ker]
  rfl

theorem source_plane_normal_core : ((f.Vi 1).subgroupOf (pairCore V H h)).Normal :=
  source_quotientPlaneProjection_ker d ▸
    (inferInstance : (source_quotientPlaneProjection d).ker.Normal)

def source_quotientPlaneEquiv :
    letI := source_plane_normal_core d
    (pairCore V H h ⧸ (f.Vi 1).subgroupOf (pairCore V H h)) ≃*
      Multiplicative (Fin 2 → S.field.Carrier) := by
  letI := source_plane_normal_core d
  exact (QuotientGroup.quotientMulEquivOfEq (source_quotientPlaneProjection_ker d).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (source_quotientPlaneProjection_surjective d))

theorem source_quotientPlaneEquiv_mk (p : pairCore V H h) :
    letI := source_plane_normal_core d
    source_quotientPlaneEquiv d (QuotientGroup.mk' _ p) = source_quotientPlaneProjection d p := rfl

theorem source_quotientPlaneProjection_conjugation (l : f.Li 1) (p : pairCore V H h) :
    (source_quotientPlaneProjection d (source_localPairAction d l p)).toAdd =
      (source_sectionActors d l).val *ᵥ (source_quotientPlaneProjection d p).toAdd := by
  apply Multiplicative.ofAdd.injective
  apply (SemidirectProduct.inl_injective (φ := Matrix.SL2.naturalAction S.field.Carrier))
  change SemidirectProduct.inl (source_quotientPlaneProjection d (source_localPairAction d l p)) =
    SemidirectProduct.inl (Matrix.SL2.naturalAction S.field.Carrier
      (source_sectionActors d l) (source_quotientPlaneProjection d p))
  rw [source_quotientPlaneProjection_inl]
  change source_localAffineProjection d
      (inclusion (source_pairCore_le_factors d).2 (source_localPairAction d l p)) =
    SemidirectProduct.inl (Matrix.SL2.naturalAction S.field.Carrier
      (source_localAffineProjection d l).right (source_quotientPlaneProjection d p))
  rw [← Matrix.SL2.conjugate_inl S.field.Carrier (source_localAffineProjection d l),
    source_quotientPlaneProjection_inl]
  change source_localAffineProjection d (l * inclusion (source_pairCore_le_factors d).2 p * l⁻¹) = _
  rw [map_mul,map_mul,map_inv]

theorem source_quotientPlaneEquiv_conjugation (l : f.Li 1) (p : pairCore V H h) :
    letI := source_plane_normal_core d
    (source_quotientPlaneEquiv d
      (QuotientGroup.mk' _ (source_localPairAction d l p))).toAdd =
      (source_sectionActors d l).val *ᵥ
        (source_quotientPlaneEquiv d (QuotientGroup.mk' _ p)).toAdd :=
  source_quotientPlaneProjection_conjugation d l p

def source_sectionPlaneCoordinates : Additive (f.Vi 1) ≃+ (Fin 2 → S.field.Carrier) :=
  (MulEquiv.subgroupCongr (congrArg (fun a : InvariantFlag (.sl3 m) => a.Vi 1)
    (source_flag_eq d))).toAdditive.trans (SL3.PlaneAction.planeEquiv D S m).toAddEquiv

def source_localPlaneAction : f.Li 1 →* MulAut (f.Vi 1) :=
  (f.Vi 1).normalizerMonoidHom.comp (inclusion ((localResidual_le _).trans inf_le_right))

theorem source_sectionPlaneCoordinates_conjugation (l : f.Li 1) (v : f.Vi 1) :
    source_sectionPlaneCoordinates d (Additive.ofMul (source_localPlaneAction (f := f) l v)) =
      (source_sectionActors d l).val *ᵥ source_sectionPlaneCoordinates d (Additive.ofMul v) := by
  let e := MulEquiv.subgroupCongr
    (congrArg (fun a : InvariantFlag (.sl3 m) => a.Li 1) (source_flag_eq d))
  let eV := MulEquiv.subgroupCongr
    (congrArg (fun a : InvariantFlag (.sl3 m) => a.Vi 1) (source_flag_eq d))
  exact SL3.PlaneAction.planeEquiv_intertwines D S m (e l) (Additive.ofMul (eV v))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)
include d

/-- The two literal sections carry the same original natural SL₂ action. -/
theorem source_local_natural_sections :
    letI := source_plane_normal_core d
    ∃ (a : f.Li 1 →* SL(2,S.field.Carrier))
      (e : Additive (f.Vi 1) ≃+ (Fin 2 → S.field.Carrier))
      (b : (pairCore V H h ⧸ (f.Vi 1).subgroupOf (pairCore V H h)) ≃*
        Multiplicative (Fin 2 → S.field.Carrier)),
      Function.Surjective a ∧ a.ker = (pairCore V H h).subgroupOf (f.Li 1) ∧
      (∀ (l : f.Li 1) (v : f.Vi 1),
        e (Additive.ofMul (source_localPlaneAction (f := f) l v)) =
          (a l).val *ᵥ e (Additive.ofMul v)) ∧
      (∀ (l : f.Li 1) (p : pairCore V H h),
        (b (QuotientGroup.mk' _ (source_localPairAction d l p))).toAdd =
          (a l).val *ᵥ (b (QuotientGroup.mk' _ p)).toAdd) := by
  let := source_plane_normal_core d
  exact ⟨source_sectionActors d,source_sectionPlaneCoordinates d,source_quotientPlaneEquiv d,
    source_sectionActors_surjective d,source_sectionActors_ker d,
    source_sectionPlaneCoordinates_conjugation d,source_quotientPlaneEquiv_conjugation d⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

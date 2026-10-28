module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.StarNormalizerAction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedAutomorphism
/-!
# Model intertwiners from the original moved section

A simultaneous normalizer of K and R acts on their actual star module.
Restriction to K* inside any containing offender group preserves the
literal moved space and its central quotient. Transporting these maps through
the supplied B.5 action equivalence gives a model automorphism and linear
intertwiner compatible with the original surjection from K.

Both the quotient and moved-space forms are retained. They apply respectively
to the natural and repeated-natural linear-three rows without reconstructing
a block or identifying its core quotient with its star image.

Source: Aschbacher–Smith C.2.7 and15.3.20, pp.145–147,1127–1128.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G D W : Type*} [Group G] [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    {K R : Subgroup G} {J : Subgroup (StarQuotient K R)}
    (hCJ : starImage K R K ≤ J)

noncomputable def starMovedProjection
    (e : (starImage K R K).subgroupOf J ≃* D) : K →* D :=
  e.toMonoidHom.comp (((subgroupOfEquivOfLe hCJ).symm.toMonoidHom).comp (toStarImage K R))

theorem starMovedProjection_surjective
    (e : (starImage K R K).subgroupOf J ≃* D) :
    Function.Surjective (starMovedProjection hCJ e) :=
  e.surjective.comp ((subgroupOfEquivOfLe hCJ).symm.surjective.comp (toStarImage_surjective K R))

noncomputable def starMovedActor (a : G)
    (hK : a ∈ normalizer (K : Set G)) (hR : a ∈ normalizer (R : Set G)) :
    MulAut ((starImage K R K).subgroupOf J) :=
  (subgroupOfEquivOfLe hCJ).trans
    ((starComponentAut K R a hK hR).trans (subgroupOfEquivOfLe hCJ).symm)

theorem starMovedActor_intertwines (a : G) (hK) (hR)
    (l : (starImage K R K).subgroupOf J) (v : Additive (starV K R)) :
    starVectorAut K R a hK hR ((starRepresentation K R).comp J.subtype l v) =
      (starRepresentation K R).comp J.subtype (starMovedActor hCJ a hK hR l)
        (starVectorAut K R a hK hR v) := by
  have hh := starNormalizerAut_intertwines K R a hK hR (l.val.val) v
  have he := starComponentAut_coe K R a hK hR ((subgroupOfEquivOfLe hCJ) l)
  change (starComponentAut K R a hK hR ((subgroupOfEquivOfLe hCJ) l) : StarQuotient K R) =
    starNormalizerAut K R a hK hR l.val.val at he
  change starVectorAut K R a hK hR (starRepresentation K R l.val.val v) =
    starRepresentation K R (starComponentAut K R a hK hR ((subgroupOfEquivOfLe hCJ) l))
      (starVectorAut K R a hK hR v)
  rw [he]
  exact hh

theorem starMovedProjection_equivariant
    (e : (starImage K R K).subgroupOf J ≃* D) (a : G) (hK) (hR) (k : K) :
    starMovedProjection hCJ e (K.normalizerMonoidHom ⟨a,hK⟩ k) =
      (e.symm.trans ((starMovedActor hCJ a hK hR).trans e))
        (starMovedProjection hCJ e k) := by
  change e ((subgroupOfEquivOfLe hCJ).symm (toStarImage K R _)) =
    e (starMovedActor hCJ a hK hR (e.symm (e ((subgroupOfEquivOfLe hCJ).symm
      (toStarImage K R k)))))
  rw [e.symm_apply_apply]
  change e ((subgroupOfEquivOfLe hCJ).symm (toStarImage K R _)) =
    e ((subgroupOfEquivOfLe hCJ).symm (starComponentAut K R a hK hR
      ((subgroupOfEquivOfLe hCJ) ((subgroupOfEquivOfLe hCJ).symm (toStarImage K R k)))))
  rw [MulEquiv.apply_symm_apply,starComponentAut_toStarImage]

variable (s : MovedSection ((starRepresentation K R).comp J.subtype)
    ((starImage K R K).subgroupOf J))
    {σ : Representation (ZMod 2) D W}

theorem starMovedSection_model_intertwiner
    (e : ActionEquiv (s.action.comp ((starImage K R K).subgroupOf J).subtype) σ)
    (a : G) (hK : a ∈ normalizer (K : Set G)) (hR : a ∈ normalizer (R : Set G)) :
    ∃ α : MulAut D, ∃ f : W ≃ₗ[ZMod 2] W,
      (∀ k : K, starMovedProjection hCJ e.groupEquiv (K.normalizerMonoidHom ⟨a,hK⟩ k) =
        α (starMovedProjection hCJ e.groupEquiv k)) ∧
      ∀ g w, f (σ g w) = σ (α g) (f w) := by
  let β := starMovedActor hCJ a hK hR
  let b := starVectorAut K R a hK hR
  have hb := starMovedActor_intertwines hCJ a hK hR
  let E := s.twistedActionEquiv β b hb
  refine ⟨e.groupEquiv.symm.trans (β.trans e.groupEquiv),
    e.linearEquiv.symm.trans (E.linearEquiv.trans e.linearEquiv),?_,?_⟩
  · exact starMovedProjection_equivariant hCJ e.groupEquiv a hK hR
  · exact e.conjugate_intertwiner β E.linearEquiv (s.twistedActionEquiv_intertwines β b hb)

theorem starMovedSpace_model_intertwiner
    (e : ActionEquiv (s.space.toRepresentation.comp ((starImage K R K).subgroupOf J).subtype) σ)
    (a : G) (hK : a ∈ normalizer (K : Set G)) (hR : a ∈ normalizer (R : Set G)) :
    ∃ α : MulAut D, ∃ f : W ≃ₗ[ZMod 2] W,
      (∀ k : K, starMovedProjection hCJ e.groupEquiv (K.normalizerMonoidHom ⟨a,hK⟩ k) =
        α (starMovedProjection hCJ e.groupEquiv k)) ∧
      ∀ g w, f (σ g w) = σ (α g) (f w) := by
  let β := starMovedActor hCJ a hK hR
  let b := starVectorAut K R a hK hR
  have hb := starMovedActor_intertwines hCJ a hK hR
  let E := s.twistedSpaceEquiv β b hb
  refine ⟨e.groupEquiv.symm.trans (β.trans e.groupEquiv),
    e.linearEquiv.symm.trans (E.trans e.linearEquiv),?_,?_⟩
  · exact starMovedProjection_equivariant hCJ e.groupEquiv a hK hR
  · exact e.conjugate_intertwiner β E (s.twistedSpaceEquiv_intertwines β b hb)

end CFSG.Quasithin.ChapterC.C27Source

module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSevenStarNormality
public import Theory.Representation.BinaryAlternatingSevenControl.InnerIntertwiner
public import Theory.GroupTheory.PerfectCentralCoverInnerLift
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.MovedProjectionEquation

/-!
# Inner component actions in the exceptional A₇ four-space

The actual simultaneous normalizers of L and R act on the canonical moved
quotient. In a faithful binary A₇ four-space an intertwining linear map belongs
to the A₇ image, because that image is self-normalizing in GL₄(2). Thus the
induced star-component automorphism is inner. Uniqueness of maps from a perfect
group through a central extension lifts this innerness to L/O₂(L), retaining
both its ordinary and triple-cover possibilities.

The original component catalogue supplies normalization by Y₊S. The final
producer gives the literal quotient action of S needed by the second-choice
cubic-center contradiction; it assumes no restriction on the star kernel.
Generic moved-action and cover-lifting steps are separated to preserve the
exact module instances and keep elaboration within the default budget.

Source: Aschbacher–Smith C.1.23(2),C.2.7 and15.3.21, pp.130,145–147,1127.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

private noncomputable def exceptional_relabel_action
    {D E W : Type*} [Group D] [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (e : D ≃* E) :
    ActionEquiv ρ (ρ.comp e.symm.toMonoidHom) where
  groupEquiv := e
  linearEquiv := LinearEquiv.refl (ZMod 2) W
  intertwines g v := by
    change ρ g v = ρ (e.symm (e g)) v
    rw [e.symm_apply_apply]

omit [Finite G] in
private theorem coreStar_inner_from_projection
    {K R : Subgroup G} {D : Type*} [Group D]
    (hR : R ≤ normalizer (K : Set G))
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : starImage K R K ≃* D) (hne : starImage K R K ≠ ⊥)
    (a : normalizer (K : Set G)) (α : MulAut D)
    (he : ∀ l : K, e (toStarImage K R (K.normalizerMonoidHom a l)) =
      α (e (toStarImage K R l)))
    (hi : ∃ y, α = MulAut.conj y) :
    ∃ k : K ⧸ pCore 2 K,
      quotientAut (pCore 2 K) (K.normalizerMonoidHom a) = MulAut.conj k := by
  let F : PerfectCentralCovering.Cover (K ⧸ pCore 2 K) D :=
    { toMonoidHom := e.toMonoidHom.comp (coreToStar hR)
      surjective := e.surjective.comp (coreToStar_surjective hR)
      isPerfect := hq.toIsPerfect
      ker_le_center := by
        intro x hx
        apply coreToStar_ker_le_center hR hq hne
        exact e.injective ((show e (coreToStar hR x) = 1 from hx).trans e.map_one.symm) }
  apply F.inner_of_equivariant_inner (quotientAut (pCore 2 K) (K.normalizerMonoidHom a)) α _ hi
  intro x
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
  rw [quotientAut_apply_mk]
  change e (coreToStar hR (QuotientGroup.mk' (pCore 2 K) (K.normalizerMonoidHom a l))) =
    α (e (coreToStar hR (QuotientGroup.mk' (pCore 2 K) l)))
  rw [coreToStar_mk,coreToStar_mk]
  exact he l

private theorem starMovedProjection_inner
    {K R : Subgroup G} {J : Subgroup (StarQuotient K R)}
    (hCJ : starImage K R K ≤ J)
    (s : MovedSection ((starRepresentation K R).comp J.subtype)
      ((starImage K R K).subgroupOf J))
    (hfaith : Function.Injective (MovedSection.action ((starRepresentation K R).comp J.subtype) s))
    (e : (starImage K R K).subgroupOf J ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4)
    (a : G) (hK : a ∈ normalizer (K : Set G)) (hR : a ∈ normalizer (R : Set G)) :
    ∃ α : MulAut (alternatingGroup (Fin 7)), (∃ g, α = MulAut.conj g) ∧
      ∀ k : K, ChapterC.C27Source.starMovedProjection hCJ e (K.normalizerMonoidHom ⟨a,hK⟩ k) =
        α (ChapterC.C27Source.starMovedProjection hCJ e k) := by
  let τ := (MovedSection.action ((starRepresentation K R).comp J.subtype) s).comp
    ((starImage K R K).subgroupOf J).subtype
  let σ := τ.comp e.symm.toMonoidHom
  let E := exceptional_relabel_action τ e
  obtain ⟨α,f,he,hf⟩ := ChapterC.C27Source.starMovedSection_model_intertwiner hCJ s E a hK hR
  have hσ : Function.Injective σ := hfaith.comp (Subtype.val_injective.comp e.symm.injective)
  have hi := Representation.BinaryAlternatingSevenControl.inner_of_intertwiner σ hσ hd α f hf
  have hEg : E.groupEquiv = e := rfl
  refine ⟨α,hi,?_⟩
  intro k
  have hel := he k
  rw [hEg] at hel
  exact hel

theorem raw_exceptionalSeven_normalizer_core_inner
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G)) :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J))
      (_hfaith : Function.Injective (MovedSection.action ((starRepresentation c.L d.R).comp J.subtype) s))
      (_e : (C.subgroupOf J) ≃* alternatingGroup (Fin 7))
      (_hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4)
      (a : normalizer (c.L : Set G)), (a : G) ∈ normalizer (d.R : Set G) →
      ∃ k : c.L ⧸ pCore 2 c.L,
        quotientAut (pCore 2 c.L) (c.L.normalizerMonoidHom a) = MulAut.conj k := by
  intro C J hCJ s hfaith e hd a haR
  obtain ⟨α,hi,he⟩ := starMovedProjection_inner hCJ s hfaith e hd (a : G) a.property haR
  let eC : C ≃* alternatingGroup (Fin 7) := (subgroupOfEquivOfLe hCJ).symm.trans e
  have hne : C ≠ ⊥ := by
    let : Nontrivial C := eC.symm.injective.nontrivial
    exact (nontrivial_iff_ne_bot _).mp inferInstance
  apply coreStar_inner_from_projection hR c.core_quotient_quasisimple eC hne a α _ hi
  intro l
  have hel := he l
  rw [ChapterC.C27Source.starMovedProjection_apply,
    ChapterC.C27Source.starMovedProjection_apply] at hel
  exact hel

theorem source_raw_exceptionalSeven_sylow_inner
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I) :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J))
      (_hfaith : Function.Injective (MovedSection.action ((starRepresentation c.L d.R).comp J.subtype) s))
      (_e : (C.subgroupOf J) ≃* alternatingGroup (Fin 7))
      (_hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4),
    d.Yplus ⊔ d.S ≤ normalizer (c.L : Set G) ∧
      ∀ a : normalizer (c.L : Set G), (a : G) ∈ d.S →
      ∃ k : c.L ⧸ pCore 2 c.L,
        quotientAut (pCore 2 c.L) (c.L.normalizerMonoidHom a) = MulAut.conj k := by
  intro C J hCJ s hfaith e hd
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have hS := (OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI).sylow
  let eC : C ≃* alternatingGroup (Fin 7) := (subgroupOfEquivOfLe hCJ).symm.trans e
  have hnL := alternatingSeven_star_component_normal hG d hI hf c hS h.normalizes eC
  have hn : d.Yplus ⊔ d.S ≤ normalizer (c.L : Set G) :=
    hI.1.2.trans ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp hnL)
  have hnR : d.Yplus ⊔ d.S ≤ normalizer (d.R : Set G) :=
    (d.Yplus ⊔ d.S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  refine ⟨hn,fun a ha => ?_⟩
  exact raw_exceptionalSeven_normalizer_core_inner d c h.normalizes hCJ s hfaith e hd a
    (hnR ((le_sup_right : d.S ≤ d.Yplus ⊔ d.S) ha))
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

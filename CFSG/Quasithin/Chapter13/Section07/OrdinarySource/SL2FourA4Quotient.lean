module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.ComponentNormality
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.CoverSeed
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.Extensions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.BorelSource.Images
public import Theory.Representation.SL2FourNaturalOrbits.ResidualRecognition
public import Theory.Representation.SL2FourNaturalOrbits.PointCommutator
/-!
# The original local residual in the natural SL₂(4) case

The selected normal component supplies its actual natural central cover. The
source seed plane embeds under this cover and is invariant under the local
residual. The nontrivial two-perfect residual, normalized by the component
Sylow subgroup, is therefore A₄. Restricting the original H-star quotient map
then identifies its kernel with the restriction of O₂(H).

Source: Aschbacher–Smith, 13.7.13 and the SL₂(4) case of 13.7.21,
printed pp.943 and 945–946.
-/
public section
open Subgroup Representation Representation.BinaryOffender Module
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section08.Source
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionParabolic.Marking CompatibleFlags
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ModelExclusions
open Section08.Components.Suzuki.BorelSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Utilde H V₃ V₁)]
include d

/-- The local residual has its actual A₄ image in H/O₂(H). -/
theorem source_sl2Four_residual_star_equiv
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Hstar H) (Additive (Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* SL2FourNatural.SL)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH SL2FourNatural.PointCommutator.representation eK) :
    Nonempty (starImage H (sourceOne L T V₁) ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨_,hgen⟩ := component_normal_and_span_of_one_le d hH hF9 hKH hK hL₁K
  obtain ⟨p,hp⟩ := exists_cover_of_section hKH hK ρ hρ hgen.symm
    SL2FourNatural.PointCommutator.representation eK hs
  let C := starImage H K
  let J₀ := starImage H (sourceOne L T V₁)
  have hL₁H := hL₁K.trans hKH
  have hJC : J₀ ≤ C := map_mono (comap_mono hL₁K)
  have hKn := (component_normal_and_span_of_one_le d hH hF9 hKH hK hL₁K).1
  let : C.Normal := ((normal_subgroupOf_iff_le_normalizer hKH).mpr hKn).map
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  let c := componentModelEquiv hKH hK eK
  let a := modelActor hKH hK eK
  have hac : a.comp c.toMonoidHom = C.subtype := by
    ext k
    exact modelActor_componentModelEquiv hKH hK eK k
  let S := (T.subtype hF9.T_le_H).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hS : (S : Subgroup (Hstar H)) = starImage H (T : Subgroup G) := rfl
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal C
  let R' := R.mapSurjective (f := c.toMonoidHom) c.surjective
  let J := (J₀.subgroupOf C).map c.toMonoidHom
  have hJa : J.map a = J₀ := by
    rw [map_map,hac,map_subgroupOf_eq_of_le hJC]
  have hJ : IsPPerfect 2 J := by
    have hj := starImage_twoPerfect H (sourceOne L T V₁) hL₁H
      (isPPerfect_embedded_pResidual 2 ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G)))
    have hj' := hj.of_surjective (subgroupOfEquivOfLe hJC).symm.toMonoidHom
      (subgroupOfEquivOfLe hJC).symm.surjective
    exact hj'.of_surjective (c.toMonoidHom.subgroupMap (J₀.subgroupOf C))
      (c.toMonoidHom.subgroupMap_surjective _)
  have hJne : J ≠ ⊥ := by
    intro hz
    have hz₀ : J₀ = ⊥ := by rw [←hJa,hz,Subgroup.map_bot]
    have hQ : sourceOne L T V₁ ≤ QH H := by
      intro x hx
      have hx₀ : QuotientGroup.mk' (pCore 2 H) ⟨x,hL₁H hx⟩ ∈ J₀ :=
        mem_map_of_mem _ hx
      rw [hz₀,mem_bot] at hx₀
      exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp hx₀)
    have hbad : V₃ ≤ V₁ := (seed_commutator_point_residual d).symm.le.trans
      ((commutator_mono (le_conjugateSpanBy V₃ H) hQ).trans hF9.commutator_UH_QH_le_point)
    exact not_le_of_gt hF9.point_lt hbad
  have hTJ : starImage H (T : Subgroup G) ≤ normalizer (J₀ : Set (Hstar H)) :=
    starImage_normalizes H (sourceOne L T V₁) (T : Subgroup G)
      (T_normalizes_one L T V₁ d.line_stable)
  have hRn : (R : Subgroup C) ≤ normalizer (J₀.subgroupOf C : Set C) := by
    rw [hR,←subgroupOf_normalizer_eq hJC,hS]
    exact comap_mono hTJ
  have hR'n : (R' : Subgroup (SL2FourNatural.SL)) ≤ normalizer (J : Set _) :=
    (map_mono hRn).trans (le_normalizer_map _)
  have hker (u) (hu : p u = 0) (l : sourceOne L T V₁) :
      ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hL₁H l)) u = u := by
    have hh := hp.2.1 hu (eK (QuotientGroup.mk' (pCore 2 K) ⟨l,hL₁K l.property⟩))
    have hie : inclusion hKH (⟨l,hL₁K l.property⟩ : K) = inclusion hL₁H l := Subtype.ext rfl
    simpa only [MonoidHom.comp_apply,modelActor_mk,hie] using hh
  have hpi := seed_cover_injective d hL₁H ρ hρ p.toLinearMap hker
  let W := (sectionImage H V₃ V₁ V₃).map p.toLinearMap
  have hW : Nat.card W = 4 := by
    have hd : finrank (ZMod 2) W = 2 := by
      change finrank (ZMod 2) ((sectionImage H V₃ V₁ V₃).map p.toLinearMap) = 2
      rw [←LinearMap.range_domRestrict,LinearMap.finrank_range_of_inj hpi]
      exact sectionImage_seed_finrank (d.line_le_plane.trans d.plane_le_seed) d.line_card d.seed_card
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    decide
  have hstable : ∀ g ∈ J, ∀ v ∈ W, SL2FourNatural.action g v ∈ W := by
    intro g hg v hv
    obtain ⟨u,hu,rfl⟩ := hv
    have hag : a g ∈ J₀ := by
      rw [←hJa]
      exact mem_map_of_mem a hg
    have hlocal : a g ∈ starImage H (normalizer (V₃ : Set G)) :=
      map_mono (comap_mono (point_residual_normalizes_seed d)) hag
    obtain ⟨k,hk,hke⟩ := hlocal
    refine ⟨ρ (a g) u,?_,?_⟩
    · rw [←hke]
      exact sectionImage_invariant ρ hρ V₃ k hk u hu
    · exact IntertwiningMap.isIntertwining _ _ p g u
  obtain ⟨ej⟩ := SL2FourNatural.residual_alternatingFour R' J hJ hJne hR'n
    (SL2FourNatural.subgroup_ne_top_of_invariant_plane J W hW hstable)
  exact ⟨((subgroupOfEquivOfLe hJC).symm.trans
    (c.subgroupMap (J₀.subgroupOf C))).trans ej⟩

/-- The A4 map has precisely the restriction of O2(H), not the LT two-core. -/
theorem source_sl2Four_residual_surjection
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Hstar H) (Additive (Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* SL2FourNatural.SL)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH SL2FourNatural.PointCommutator.representation eK) :
    ∃ f : sourceOne L T V₁ →* alternatingGroup (Fin 4), Function.Surjective f ∧
      f.ker = (H.pCoreIn 2).subgroupOf (sourceOne L T V₁) := by
  obtain ⟨e⟩ := source_sl2Four_residual_star_equiv d hH hF9 hKH hK hL₁K ρ hρ eK hs
  let hLH := hL₁K.trans hKH
  let q : ((sourceOne L T V₁).subgroupOf H) →* starImage H (sourceOne L T V₁) :=
    (QuotientGroup.mk' (pCore 2 H)).subgroupMap ((sourceOne L T V₁).subgroupOf H)
  let j := (subgroupOfEquivOfLe hLH).symm
  let f := e.toMonoidHom.comp (q.comp j.toMonoidHom)
  refine ⟨f,e.surjective.comp (((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _).comp
    j.surjective),?_⟩
  ext x
  change e (q (j x)) = 1 ↔ (x : G) ∈ H.pCoreIn 2
  rw [e.map_eq_one_iff,Subtype.ext_iff]
  change QuotientGroup.mk' (pCore 2 H) (inclusion hLH x) = 1 ↔ _
  constructor
  · intro hx
    exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp hx)
  · rintro ⟨y,hy,he⟩
    have hh : y = inclusion hLH x := Subtype.ext he
    exact (QuotientGroup.eq_one_iff _).mpr (hh ▸ hy)
end CFSG.Quasithin.Chapter13.Section07.OrdinarySource

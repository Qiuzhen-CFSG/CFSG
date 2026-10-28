module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SixFlags
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.SixGeneration.CoreCover
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.SymmetricSixModel
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.BorelSource.Images

/-!
# The literal alternating-four quotient in the selected six-letter branch

The faithful H/O₂(H) action and the marked natural seed plane put the
point-residual image inside A₆. The original component Sylow normalizes
this nontrivial two-perfect image. The finite plane-residual calculation
therefore identifies it with a conjugate syntheme A₄. Restricting the
actual star quotient gives a surjection with kernel O₂(H) ∩ L₁.

This is the quotient contributing the additional chief factor in the
original six-chief lower bound; the LT two-core is not used as its kernel.
Source: Aschbacher--Smith, 13.7.6(3a), 13.7.10(8), and 13.7.21,
printed pp.939, 942, and 946.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation Module
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section08.Source
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionParabolic.Marking CompatibleFlags
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open ModelExclusions
open Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics
open Section05.ComponentReduction.ChiefCount.SymmetricSixModel
open Section08.Components.Suzuki.BorelSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Utilde H V₃ V₁)]
include d

private theorem residual_equiv_of_marked_plane
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Hstar H) (Additive (Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (f : Hstar H →* Equiv.Perm (Fin 6)) (hf : Function.Injective f)
    (F : Additive (Utilde H V₃ V₁) →ₗ[ZMod 2] natural (Fin 6))
    (he : ∀ a u, F (ρ a u) = naturalRepresentation (Fin 6) (f a) (F u))
    (hplane : (sectionImage H V₃ V₁ V₃).map F = canonicalPlane) :
    Nonempty (starImage H (sourceOne L T V₁) ≃* alternatingGroup (Fin 4)) := by
  let C := starImage H K
  let J₀ := starImage H (sourceOne L T V₁)
  have hL₁H := hL₁K.trans hKH
  have hJC : J₀ ≤ C := map_mono (comap_mono hL₁K)
  have hKn := (component_normal_and_span_of_one_le d hH hF9 hKH hK hL₁K).1
  let : C.Normal := ((normal_subgroupOf_iff_le_normalizer hKH).mpr hKn).map
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  let eC := componentModelEquiv hKH hK eK
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := eC.symm.toMonoidHom) eC.symm.surjective
  let : Group.IsPerfect (C.map f) := Group.IsPerfect.map _
  have hcmap : C.map f = alternatingGroup (Fin 6) := by
    apply eq_of_le_of_card_ge
    · intro x hx
      exact Equiv.Perm.mem_alternatingGroup.mpr
        (Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp (C.map f).subtype)
          (Group.IsPerfect.mem_commutator (g := ⟨x,hx⟩)))
    · rw [card_map_of_injective hf, Nat.card_congr eC.toEquiv]
  let c : C ≃* alternatingGroup (Fin 6) :=
    (C.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hcmap)
  let a : alternatingGroup (Fin 6) →* Hstar H := C.subtype.comp c.symm.toMonoidHom
  have hac : a.comp c.toMonoidHom = C.subtype := by
    ext k
    exact congrArg Subtype.val (c.symm_apply_apply k)
  have hfa (g : alternatingGroup (Fin 6)) : f (a g) = g.val :=
    congrArg Subtype.val (c.apply_symm_apply g)
  let S := (T.subtype hF9.T_le_H).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hS : (S : Subgroup (Hstar H)) = starImage H (T : Subgroup G) := rfl
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal C
  let R' := R.mapSurjective (f := c.toMonoidHom) c.surjective
  let J := (J₀.subgroupOf C).map c.toMonoidHom
  have hJa : J.map a = J₀ := by
    rw [map_map,hac,map_subgroupOf_eq_of_le hJC]
  have hRa : (R' : Subgroup (alternatingGroup (Fin 6))).map a ≤ starImage H (T : Subgroup G) := by
    change ((R : Subgroup C).map c.toMonoidHom).map a ≤ _
    rw [map_map,hac,hR,subgroupOf_map_subtype,hS]
    exact inf_le_left
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
  have hR'n : (R' : Subgroup (alternatingGroup (Fin 6))) ≤ normalizer (J : Set _) :=
    (map_mono hRn).trans (le_normalizer_map _)
  have hE : J ⊔ (R' : Subgroup (alternatingGroup (Fin 6))) ≤
      subspaceStabilizer (alternatingNaturalRepresentation (Fin 6)) canonicalPlane := by
    have hlocal : (J ⊔ (R' : Subgroup (alternatingGroup (Fin 6)))).map a ≤
        starImage H (normalizer (V₃ : Set G)) := by
      rw [Subgroup.map_sup,hJa]
      exact sup_le (map_mono (comap_mono (point_residual_normalizes_seed d)))
        (hRa.trans (map_mono (comap_mono d.seed_stable)))
    apply le_subspaceStabilizer
    intro g hg v hv
    rw [←hplane] at hv ⊢
    obtain ⟨u,hu,rfl⟩ := hv
    obtain ⟨k,hk,hke⟩ := hlocal (mem_map_of_mem a hg)
    refine ⟨ρ (a g) u,?_,?_⟩
    · rw [←hke]
      exact sectionImage_invariant ρ hρ V₃ k hk u hu
    · rw [he,hfa]
      rfl
  obtain ⟨g,hg⟩ := SixGeneration.residual_marking R' J hJ hJne hR'n
    canonicalPlane canonicalPlane_finrank hE
  exact ⟨((subgroupOfEquivOfLe hJC).symm.trans
    (c.subgroupMap (J₀.subgroupOf C))).trans
      ((MulEquiv.subgroupCongr hg).trans (conjugateResidualEquiv g))⟩

/-- The literal local residual in the selected natural six packet has A4 star image. -/
theorem source_six_residual_star_equiv
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Hstar H) (Additive (Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin 6)) eK) :
    Nonempty (starImage H (sourceOne L T V₁) ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨_,hcases⟩ := six_seed_marking_of_one_le d hH hF9 hKH hK hL₁K ρ hρ eK hs
  rcases hcases with ⟨f,E,hf,he,_,hp⟩ | ⟨f,E,hf,he,_,hp⟩
  · exact residual_equiv_of_marked_plane d hH hF9 hKH hK hL₁K ρ hρ eK f hf E.toLinearMap he
      (hp.trans plane_image_eq_canonical)
  · let F := (coreToNatural (Fin 6)).comp E.toLinearMap
    apply residual_equiv_of_marked_plane d hH hF9 hKH hK hL₁K ρ hρ eK f hf F
    · intro a u
      change coreToNatural (Fin 6) (E (ρ a u)) = _
      rw [he]
      exact coreToNatural_equivariant (f a) (E u)
    · change (sectionImage H V₃ V₁ V₃).map ((coreToNatural (Fin 6)).comp E.toLinearMap) = _
      rw [Submodule.map_comp,hp,plane_image_eq_canonical]

/-- The A4 map has precisely the restriction of O2(H), not the LT two-core. -/
theorem source_six_residual_surjection
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Hstar H) (Additive (Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin 6)) eK) :
    ∃ f : sourceOne L T V₁ →* alternatingGroup (Fin 4), Function.Surjective f ∧
      f.ker = (H.pCoreIn 2).subgroupOf (sourceOne L T V₁) := by
  obtain ⟨e⟩ := source_six_residual_star_equiv d hH hF9 hKH hK hL₁K ρ hρ eK hs
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

module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.ComponentNormality
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PlaneImage
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.CoverProjection
public import Theory.Representation.BinaryPermutation.FiveSylowSingular
public import Theory.GroupTheory.SylowNormalIntersection
/-!
# Excluding the contained degree-five natural component

The central covering projection is injective on the transitive seed plane:
a nonzero fixed kernel vector would make every nonzero seed vector equal.
The original point is fixed by T, so its image is singular in the five-letter
quadratic module. The source L₁ orbit makes all three seed vectors singular,
contradicting the Witt index one calculation.

Source: Aschbacher–Smith, 13.7.6(3), printed p.939, n=5 exclusion.
-/
@[expose] public section
open Subgroup Representation BinaryPermutation Module
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionParabolic.Marking
open Section08.TransvectionParabolic.Marking.CompatibleFlags
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d
private theorem seed_cover_injective
    (hL₁H : sourceOne L T V₁ ≤ H)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (p : Additive (Section08.Source.Utilde H V₃ V₁) →ₗ[ZMod 2] E)
    (hk : ∀ u, p u = 0 → ∀ l : sourceOne L T V₁,
      ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hL₁H l)) u = u) :
    Function.Injective (p.domRestrict (sectionImage H V₃ V₁ V₃)) := by
  apply (LinearMap.ker_eq_bot).mp
  apply _root_.eq_bot_iff.mpr
  intro u hu
  change u = 0
  by_contra hn
  have hun : u.val ≠ 0 := fun hz => hn (Subtype.ext hz)
  have hall : ∀ w ∈ sectionImage H V₃ V₁ V₃, w ≠ 0 → w = u := by
    intro w hw hw0
    obtain ⟨l,hl⟩ := seed_section_nonzero_orbit d hL₁H ρ hρ u u.property hun w hw hw0
    exact hl.symm.trans (hk u hu l)
  have he : sectionImage H V₃ V₁ V₃ = Submodule.span (ZMod 2) {u.val} := by
    apply le_antisymm
    · intro w hw
      by_cases hz : w = 0
      · exact hz ▸ Submodule.zero_mem _
      · rw [hall w hw hz]
        exact Submodule.subset_span (by simp)
    · exact Submodule.span_le.mpr (by rintro w rfl; exact u.property)
  have hd := sectionImage_seed_finrank (d.line_le_plane.trans d.plane_le_seed) d.line_card d.seed_card (H := H)
  rw [he,finrank_span_singleton hun] at hd
  omega

private theorem plane_vector_fixed
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (t : H) (ht : (t : G) ∈ (T : Subgroup G))
    (u : Additive (Section08.Source.Utilde H V₃ V₁))
    (hu : u ∈ sectionImage H V₃ V₁ V₂) (hu0 : u ≠ 0) :
    ρ (QuotientGroup.mk' (pCore 2 H) t) u = u := by
  have hs := sectionImage_invariant ρ hρ V₂ t (d.plane_stable ht) u hu
  have he : sectionImage H V₃ V₁ V₂ = Submodule.span (ZMod 2) {u} :=
    (eq_span_singleton_of_mem_of_finrank_eq_one (plane_section_finrank d) hu hu0)
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp (he ▸ hs)
  have hac : a = 0 ∨ a = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) a
  rcases hac with rfl | rfl
  · have hz : ρ (QuotientGroup.mk' (pCore 2 H) t) u = 0 := by simpa using ha.symm
    exact (hu0 ((ρ.apply_bijective _).1 (hz.trans (map_zero _).symm))).elim
  · simpa using ha.symm

/-- The original contained component cannot have the five-letter natural section. -/
theorem not_five_natural_of_one_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    ¬ HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin 5)) eK := by
  intro hs
  obtain ⟨hKn,hgen⟩ := component_normal_and_span_of_one_le d hH hF9 hKH hK hL₁K
  obtain ⟨p,hp⟩ := exists_cover_of_section hKH hK ρ hρ hgen.symm
    (alternatingNaturalRepresentation (Fin 5)) eK hs
  let c := coreEquivNatural (Fin 5) (by decide)
  let F := c.symm.toLinearMap.comp p.toLinearMap
  let hL₁H := hL₁K.trans hKH
  have hFe (k : K) (u) : F (ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) u) =
      alternatingCoreRepresentation (Fin 5) (eK (QuotientGroup.mk' (pCore 2 K) k)) (F u) := by
    apply c.injective
    change c (c.symm (p (ρ _ u))) = c (coreRepresentation (Fin 5) _ (c.symm (p u)))
    rw [c.apply_symm_apply,coreEquivNatural_equivariant,c.apply_symm_apply]
    have he := IntertwiningMap.isIntertwining _ _ p (eK (QuotientGroup.mk' (pCore 2 K) k)) u
    simpa only [MonoidHom.comp_apply,modelActor_mk] using he
  have hker (u) (hu : F u = 0) (l : sourceOne L T V₁) :
      ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hL₁H l)) u = u := by
    have hpu : p u = 0 := c.symm.injective (hu.trans (map_zero c.symm).symm)
    have hh := hp.2.1 hpu (eK (QuotientGroup.mk' (pCore 2 K) ⟨l,hL₁K l.property⟩))
    have hie : inclusion hKH (⟨l,hL₁K l.property⟩ : K) = inclusion hL₁H l := Subtype.ext rfl
    simpa only [MonoidHom.comp_apply,modelActor_mk,hie] using hh
  have hFi := seed_cover_injective d hL₁H ρ hρ F hker
  let P := sectionImage H V₃ V₁ V₃
  let D := P.map F
  have hd : finrank (ZMod 2) D = 2 := by
    change finrank (ZMod 2) (P.map F) = 2
    rw [←LinearMap.range_domRestrict,LinearMap.finrank_range_of_inj hFi]
    exact sectionImage_seed_finrank (d.line_le_plane.trans d.plane_le_seed) d.line_card d.seed_card
  have hP₂ : sectionImage H V₃ V₁ V₂ ≠ ⊥ := by
    intro hz
    have hh := plane_section_finrank d (H := H)
    rw [hz,finrank_bot] at hh
    omega
  obtain ⟨u,hu,hu0⟩ := (Submodule.ne_bot_iff _).mp hP₂
  have huP : u ∈ P := by
    obtain ⟨v,hv,rfl⟩ := hu
    exact ⟨v,d.plane_le_seed hv,rfl⟩
  have hFu : F u ≠ 0 := by
    intro hz
    have hh := hFi (a₁ := ⟨u,huP⟩) (a₂ := 0) (hz.trans (map_zero _).symm)
    exact hu0 (congrArg Subtype.val hh)
  let KN := K.subgroupOf H
  let : KN.Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hTH : (T : Subgroup G) ≤ H := hF9.T_le_H
  obtain ⟨Q,hQ⟩ := (T.subtype hTH).exists_subgroupOf_eq_of_normal KN
  let e0 : KN ≃* K := subgroupOfEquivOfLe hKH
  let q := eK.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 K)).comp e0.toMonoidHom)
  have hq : Function.Surjective q := eK.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp e0.surjective)
  let Q₅ := Q.mapSurjective hq
  have hfixed : ∀ g ∈ Q₅, alternatingCoreRepresentation (Fin 5) g (F u) = F u := by
    rintro g ⟨k,hk,rfl⟩
    change alternatingCoreRepresentation (Fin 5) (eK (QuotientGroup.mk' (pCore 2 K) (e0 k))) (F u) = _
    rw [←hFe]
    apply congrArg F
    apply plane_vector_fixed d ρ hρ _ _ u hu hu0
    have ht : k ∈ ((T.subtype hTH : Sylow 2 H) : Subgroup H).subgroupOf KN := hQ ▸ hk
    exact ht
  have hsing := FiveSylowSingular.fixed_singular Q₅ (F u) hfixed
  have hsingD : ∀ v ∈ D, FiveGeometry.form v = 0 := by
    rintro v ⟨v',hv',rfl⟩
    by_cases hv0 : v' = 0
    · simp only [hv0,map_zero]
    obtain ⟨l,hl⟩ := seed_section_nonzero_orbit d hL₁H ρ hρ u huP hu0 v' hv' hv0
    have he := hFe (⟨l,hL₁K l.property⟩ : K) u
    have hie : inclusion hKH (⟨l,hL₁K l.property⟩ : K) = inclusion hL₁H l := Subtype.ext rfl
    rw [hie,hl] at he
    rw [he]
    exact FiveTensorFixedLine.singular_permute _ _ hsing
  let b := finBasisOfFinrankEq (ZMod 2) D hd
  have hx : (b 0 : core (Fin 5)) ≠ 0 := fun hz => b.ne_zero 0 (Subtype.ext hz)
  have hy : (b 1 : core (Fin 5)) ≠ 0 := fun hz => b.ne_zero 1 (Subtype.ext hz)
  have hxy := FiveGeometry.singular_add (b 0) (b 1)
    (hsingD _ (b 0).property) (hsingD _ (b 1).property)
    (hsingD _ (D.add_mem (b 0).property (b 1).property))
  have he := (hxy.resolve_left hx).resolve_left hy
  exact (by decide : (0 : Fin 2) ≠ 1) (b.injective (Subtype.ext he))
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions

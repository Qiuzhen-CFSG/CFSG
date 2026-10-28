module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.ContainedAlternating
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedTransitivity
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PlaneImage
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.CompatibleFlags.Geometry
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CorePlaneGeometry
/-!
# Original six-letter point and seed markings

The actual full action and the ambient Sylow subgroup simultaneously mark
V₂/V₁ and V₃/V₁. In the augmentation cover, the three nonzero seed vectors
form one L₁ orbit, so they have equal weights. The binary Sylow-plane
calculation forces weight four, which identifies both flags. All actions
remain on the original H/O₂(H) and U_H/V₁.

Source: Aschbacher–Smith, 13.7.6(3a), printed p.939. The local quotient
alternative and the chief-factor count are separate subsequent deductions.
-/
@[expose] public section
open Subgroup Representation BinaryPermutation Module
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionParabolic
open Section08.TransvectionParabolic.Marking
open Section08.TransvectionParabolic.Marking.CompatibleFlags
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d
private theorem cover_seed_weights_equal
    (hL₁H : sourceOne L T V₁ ≤ H)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (f : Section08.Source.Hstar H →* S)
    (E : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (he : ∀ a u, E (ρ a u) = coreRepresentation (Fin 6) (f a) (E u)) :
    ∀ u ∈ (sectionImage H V₃ V₁ V₃).map E.toLinearMap, u ≠ 0 →
      ∀ v ∈ (sectionImage H V₃ V₁ V₃).map E.toLinearMap, v ≠ 0 →
        OrbitModels.weight u = OrbitModels.weight v := by
  rintro u ⟨u',hu',rfl⟩ hu v ⟨v',hv',rfl⟩ hv
  have hun : u' ≠ 0 := fun hz => hu (by rw [hz,map_zero])
  have hvn : v' ≠ 0 := fun hz => hv (by rw [hz,map_zero])
  obtain ⟨l,hl⟩ := seed_section_nonzero_orbit d hL₁H ρ hρ u' hu' hun v' hv' hvn
  have ha := he (QuotientGroup.mk' (pCore 2 H) (inclusion hL₁H l)) u'
  rw [hl] at ha
  exact ((cover_weight_map _ _).symm.trans (congrArg OrbitModels.weight ha.symm))

private theorem cover_source_flags
    (hL₁H : sourceOne L T V₁ ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (f : Section08.Source.Hstar H →* S) (ha : alternatingGroup (Fin 6) ≤ f.range)
    (E : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (he : ∀ a u, E (ρ a u) = coreRepresentation (Fin 6) (f a) (E u)) :
    ∃ g : S,
      ((sectionImage H V₃ V₁ V₂).map E.toLinearMap).map (coreRepresentation (Fin 6) g⁻¹) = OrbitModels.pointSpace ∧
      ((sectionImage H V₃ V₁ V₃).map E.toLinearMap).map (coreRepresentation (Fin 6) g⁻¹) = OrbitModels.plane := by
  obtain ⟨g,_,hg⟩ := source_sylow_alignment H T hTH f ha
  let r := coreRepresentation (Fin 6)
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (r.asGroupHom g⁻¹)
  let P := (sectionImage H V₃ V₁ V₂).map E.toLinearMap
  let D := (sectionImage H V₃ V₁ V₃).map E.toLinearMap
  have hi (X : Subgroup G) (hTX : (T : Subgroup G) ≤ normalizer (X : Set G)) :=
    invariant_after_alignment r ((sectionImage H V₃ V₁ X).map E.toLinearMap)
      _ g hg (marked_section_invariant ρ hρ f r E he _ X hTX)
  have hdim : finrank (ZMod 2) (D.map (r g⁻¹)) = 2 :=
    (e.finrank_map_eq D).trans ((E.finrank_map_eq _).trans
      (sectionImage_seed_finrank (d.line_le_plane.trans d.plane_le_seed) d.line_card d.seed_card))
  have hwe : ∀ u ∈ D.map (r g⁻¹), u ≠ 0 → ∀ v ∈ D.map (r g⁻¹), v ≠ 0 →
      CorePlaneGeometry.weight u = CorePlaneGeometry.weight v := by
    rintro u ⟨u',hu',rfl⟩ hu v ⟨v',hv',rfl⟩ hv
    have hun : u' ≠ 0 := fun hz => hu (by rw [hz,map_zero])
    have hvn : v' ≠ 0 := fun hz => hv (by rw [hz,map_zero])
    change OrbitModels.weight (r g⁻¹ u') = OrbitModels.weight (r g⁻¹ v')
    rw [cover_weight_map,cover_weight_map]
    exact cover_seed_weights_equal d hL₁H ρ hρ f E he u' hu' hun v' hv' hvn
  have hw : ∀ u ∈ D.map (r g⁻¹), u ≠ 0 → OrbitModels.weight u = 4 :=
    CorePlaneGeometry.plane_weight_four _ hdim (hi V₃ d.seed_stable) hwe
  have hgen (W : Submodule (ZMod 2) (core (Fin 6))) (hW : W ≤ D.map (r g⁻¹)) :
      W = Submodule.span (ZMod 2) {v | v ∈ W ∧ OrbitModels.weight v = 4} := by
    apply le_antisymm
    · intro v hv
      by_cases hz : v = 0
      · exact hz ▸ Submodule.zero_mem _
      · exact Submodule.subset_span ⟨hv,hw v (hW hv) hz⟩
    · exact Submodule.span_le.mpr (fun _ h => h.1)
  have hPD : P ≤ D := Submodule.map_mono (by
    rintro v ⟨u,hu,rfl⟩
    exact ⟨u,d.plane_le_seed hu,rfl⟩)
  refine ⟨g,?_,?_⟩
  · apply cover_point_unique
    · exact (e.finrank_map_eq P).trans ((E.finrank_map_eq _).trans (plane_section_finrank d))
    · exact hi V₂ d.plane_stable
    · exact hgen _ (Submodule.map_mono hPD)
  · exact cover_plane_unique _ hdim (hi V₃ d.seed_stable) (hgen _ le_rfl)

omit d [Finite G] in
private theorem conjugate_full_action
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (r : Representation (ZMod 2) S W)
    (f : Section08.Source.Hstar H →* S)
    (E : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] W)
    (he : ∀ a u, E (ρ a u) = r (f a) (E u)) (g : S) :
    ∀ a u, r g⁻¹ (E (ρ a u)) =
      r (((MulAut.conj g⁻¹).toMonoidHom.comp f) a) (r g⁻¹ (E u)) := by
  intro a u
  change r g⁻¹ (E (ρ a u)) = r (g⁻¹ * f a * (g⁻¹)⁻¹) (r g⁻¹ (E u))
  rw [he]
  simp only [← Module.End.mul_apply,← map_mul,mul_assoc,inv_mul_cancel,mul_one]

/-- The original six-letter natural section supplies both literal source flags,
including the weight-four point in the augmentation alternative. -/
theorem six_seed_marking_of_one_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin 6)) eK) :
    (H : Set G) = (K : Set G) * (T : Set G) ∧
    ((∃ (f : Section08.Source.Hstar H →* S)
      (E : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6)),
      Function.Injective f ∧
      (∀ a u, E (ρ a u) = naturalRepresentation (Fin 6) (f a) (E u)) ∧
      (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.naturalPointSpace ∧
      (sectionImage H V₃ V₁ V₃).map E.toLinearMap = OrbitModels.plane.map (coreToNatural (Fin 6))) ∨
    (∃ (f : Section08.Source.Hstar H →* S)
      (E : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6)),
      Function.Injective f ∧
      (∀ a u, E (ρ a u) = coreRepresentation (Fin 6) (f a) (E u)) ∧
      (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.pointSpace ∧
      (sectionImage H V₃ V₁ V₃).map E.toLinearMap = OrbitModels.plane)) := by
  have hTH : (T : Subgroup G) ≤ H := hF9.T_le_H
  obtain ⟨hprod,hcases⟩ := contained_six_full_action d hH hF9 hKH hK hL₁K ρ hρ eK hs
  refine ⟨hprod,?_⟩
  rcases hcases with ⟨f,E,hf,hfK,he⟩ | ⟨f,E,hf,hfK,he⟩
  · have ha : alternatingGroup (Fin 6) ≤ f.range := by
      intro a ha
      obtain ⟨k,hk⟩ := (componentModelEquiv hKH hK eK).surjective ⟨a,ha⟩
      exact ⟨k,by rw [hfK,hk]⟩
    obtain ⟨g,_,hp,hd⟩ := natural_source_flags T hTH ρ hρ f ha E he
      d.plane_stable d.seed_stable (plane_section_finrank d)
      (sectionImage_seed_finrank (d.line_le_plane.trans d.plane_le_seed) d.line_card d.seed_card)
    let r := naturalRepresentation (Fin 6)
    let E' := E.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (r.asGroupHom g⁻¹))
    refine Or.inl ⟨(MulAut.conj g⁻¹).toMonoidHom.comp f,E',
      (MulAut.conj g⁻¹).injective.comp hf,conjugate_full_action ρ r f E he g,?_,?_⟩
    · change (sectionImage H V₃ V₁ V₂).map ((r g⁻¹).comp E.toLinearMap) = _
      rw [Submodule.map_comp]
      exact hp
    · change (sectionImage H V₃ V₁ V₃).map ((r g⁻¹).comp E.toLinearMap) = _
      rw [Submodule.map_comp]
      exact hd
  · have ha : alternatingGroup (Fin 6) ≤ f.range := by
      intro a ha
      obtain ⟨k,hk⟩ := (componentModelEquiv hKH hK eK).surjective ⟨a,ha⟩
      exact ⟨k,by rw [hfK,hk]⟩
    obtain ⟨g,hp,hd⟩ := cover_source_flags d (hL₁K.trans hKH) hTH ρ hρ f ha E he
    let r := coreRepresentation (Fin 6)
    let E' := E.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (r.asGroupHom g⁻¹))
    refine Or.inr ⟨(MulAut.conj g⁻¹).toMonoidHom.comp f,E',
      (MulAut.conj g⁻¹).injective.comp hf,conjugate_full_action ρ r f E he g,?_,?_⟩
    · change (sectionImage H V₃ V₁ V₂).map ((r g⁻¹).comp E.toLinearMap) = _
      rw [Submodule.map_comp]
      exact hp
    · change (sectionImage H V₃ V₁ V₃).map ((r g⁻¹).comp E.toLinearMap) = _
      rw [Submodule.map_comp]
      exact hd
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions

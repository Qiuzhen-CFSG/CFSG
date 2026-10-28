module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SixSeedRank
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.ChiefQuotient
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPlaneChief
public import Theory.Representation.ChiefCountFixedKernel
/-!
# The original six-letter chief count on U_H

The source seed orbit transports to the canonical natural plane. Its
Lagrangian geometry gives two noncentral chief factors on the natural
module. The augmentation projection has a fixed constant-line kernel,
and the original U_H→U_H/V₁ map has a fixed kernel of order two. Lifting
complete chief flags through those actual equivariant maps gives precisely
the printed count on U_H itself.

Source: Aschbacher–Smith, 13.7.6(3a), printed p.939.
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
open BinaryLinearThree.ParabolicCyclic.ChiefCounts
private theorem two_chief_of_count
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) A W) (hc : HasCount σ 2) :
    Section08.CriticalGeometry.Reorientation.TwoNoncentralChiefFactors σ := by
  obtain ⟨s,h0,h1,hs⟩ := hc
  refine ⟨s.length,s,h0,h1,s.step,?_⟩
  have heq : Nat.card {i : Fin s.length // ∃ g, ∃ v,
      Representation.BinaryOffender.sectionRepresentation σ
        (s i.castSucc) (s i.succ) g v ≠ v} =
      Nat.card {i : Fin s.length // ¬ Central (s i.castSucc) (s i.succ)} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro i
    have h : Central (s i.castSucc) (s i.succ) ↔
        ∀ g v, Representation.BinaryOffender.sectionRepresentation σ
          (s i.castSucc) (s i.succ) g v = v := by
      apply forall_congr'
      intro g
      exact (Representation.BinaryOffender.sectionRepresentation_trivial_iff
        σ (s i.castSucc) (s i.succ) g).symm
    simpa only [not_forall] using (not_congr h).symm
  exact heq.trans hs
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d
private theorem count_of_natural_image
    [IsElementaryAbelian 2 (Section08.Source.UH H V₃)]
    (hL₁H : sourceOne L T V₁ ≤ H)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (f : Section08.Source.Hstar H →* S)
    (F : Additive (Section08.Source.Utilde H V₃ V₁) →ₗ[ZMod 2] natural (Fin 6))
    (he : ∀ a u, F (ρ a u) = naturalRepresentation (Fin 6) (f a) (F u))
    (hp : Function.Surjective F)
    (hk : ∀ l u, F u = 0 → ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hL₁H l)) u = u)
    (hplane : (sectionImage H V₃ V₁ V₃).map F = canonicalPlane) :
    HasCount (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L T V₁) hL₁H ρ) 2 := by
  let q := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hL₁H)
  let g := f.comp q
  let τ := ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L T V₁) hL₁H ρ
  let r := naturalRepresentation (Fin 6)
  have hi' (l : sourceOne L T V₁) (v : natural (Fin 6)) (hv : v ∈ canonicalPlane) :
      r (g l) v ∈ canonicalPlane := by
    rw [←hplane] at hv ⊢
    obtain ⟨u,hu,rfl⟩ := hv
    refine ⟨ρ (q l) u,?_,he _ _⟩
    exact sectionImage_invariant ρ hρ V₃ (inclusion hL₁H l)
      (point_residual_normalizes_seed d l.property) u hu
  have hi (l : sourceOne L T V₁) : canonicalPlane.map (r (g l)) = canonicalPlane := by
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      exact hi' l v hv
    · intro v hv
      refine ⟨r (g l⁻¹) v,hi' l⁻¹ v hv,?_⟩
      simp only [map_inv,← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  have ho : ∀ u ∈ canonicalPlane, u ≠ 0 → ∀ v ∈ canonicalPlane, v ≠ 0 →
      ∃ l : sourceOne L T V₁, r (g l) u = v := by
    intro u hu hun v hv hvn
    rw [←hplane] at hu hv
    obtain ⟨u',hu',rfl⟩ := hu
    obtain ⟨v',hv',rfl⟩ := hv
    have hu0 : u' ≠ 0 := fun hz => hun (by rw [hz,map_zero])
    have hv0 : v' ≠ 0 := fun hz => hvn (by rw [hz,map_zero])
    obtain ⟨l,hl⟩ := seed_section_nonzero_orbit d hL₁H ρ hρ u' hu' hu0 v' hv' hv0
    exact ⟨l,(he (q l) u').symm.trans (congrArg F hl)⟩
  have hcount := NaturalPlaneChief.natural_two_noncentral g hi ho
  let p : τ.IntertwiningMap (r.comp g) := {
    toLinearMap := F
    isIntertwining' l := by
      apply LinearMap.ext
      intro u
      exact he (q l) u }
  exact HasCount.of_surjective_fixed_kernel p hp hk hcount

/-- Exactly two noncentral L₁-chief factors on the original unquotiented U_H. -/
theorem six_chief_factors_of_one_le
    [IsElementaryAbelian 2 (Section08.Source.UH H V₃)]
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin 6)) eK) :
    Section08.CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
      (ChiefQuotient.loneRepresentation H V₃ (sourceOne L T V₁) (hL₁K.trans hKH)) := by
  let hL₁H := hL₁K.trans hKH
  have hcount : HasCount (ChiefQuotient.loneQuotientRepresentation H V₃ V₁
      (sourceOne L T V₁) hL₁H ρ) 2 := by
    obtain ⟨_,hcases⟩ := six_seed_marking_of_one_le d hH hF9 hKH hK hL₁K ρ hρ eK hs
    rcases hcases with ⟨f,E,_,he,_,hplane⟩ | ⟨f,E,_,he,_,hplane⟩
    · apply count_of_natural_image d hL₁H ρ hρ f E.toLinearMap he E.surjective
      · intro l u hu
        have hu0 : u = 0 := E.injective (hu.trans (map_zero E).symm)
        rw [hu0,map_zero]
      · exact hplane.trans plane_image_eq_canonical
    · let F := (coreToNatural (Fin 6)).comp E.toLinearMap
      have he' : ∀ a u, F (ρ a u) = naturalRepresentation (Fin 6) (f a) (F u) := by
        intro a u
        change coreToNatural (Fin 6) (E (ρ a u)) = _
        rw [he]
        exact coreToNatural_equivariant (f a) (E u)
      apply count_of_natural_image d hL₁H ρ hρ f F he'
        (coreToNatural_surjective.comp E.surjective)
      · intro l u hu
        have hk : E u ∈ (coreToNatural (Fin 6)).ker := hu
        rw [OrbitModels.natural_kernel] at hk
        obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hk
        apply E.injective
        rw [he,←hc,map_smul]
        congr 1
        apply Subtype.ext
        funext i
        have hh : OrbitModels.constant.val = allOne (Fin 6) := by
          funext j
          fin_cases j <;> rfl
        change OrbitModels.constant.val ((f _).symm i) = OrbitModels.constant.val i
        rw [hh]
        rfl
      · change (sectionImage H V₃ V₁ V₃).map ((coreToNatural (Fin 6)).comp E.toLinearMap) = _
        rw [Submodule.map_comp,hplane,plane_image_eq_canonical]
  have hV₁ : V₁ ≤ Section08.Source.UH H V₃ :=
    (d.line_le_plane.trans d.plane_le_seed).trans (le_conjugateSpanBy V₃ H)
  have hfull := HasCount.of_surjective_fixed_kernel
    (ChiefQuotient.quotientIntertwiner H V₃ V₁ (sourceOne L T V₁) hL₁H ρ hρ)
    (ChiefQuotient.quotientIntertwiner_surjective H V₃ V₁ (sourceOne L T V₁) hL₁H ρ hρ)
    (ChiefQuotient.quotientKernel_fixed H V₃ V₁ (sourceOne L T V₁) hL₁H ρ hρ hV₁ d.line_card)
    hcount
  exact two_chief_of_count _ hfull
/-- All algebraic conclusions of original 13.7.6(3a) for the contained
six-letter component, including the chief count on U_H itself. The simultaneous
printed point and plane coordinates are supplied by six_seed_marking_of_one_le. -/
theorem six_source_case_of_one_le
    [IsElementaryAbelian 2 (Section08.Source.UH H V₃)]
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin 6)) eK) :
    Section08.Source.UH H V₃ = ⁅Section08.Source.UH H V₃,K⁆ ∧
    (H : Set G) = (K : Set G) * (T : Set G) ∧
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
    Section08.CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
      (ChiefQuotient.loneRepresentation H V₃ (sourceOne L T V₁) (le_sup_left.trans hH.1.2)) := by
  exact ⟨(component_normal_and_span_of_one_le d hH hF9 hKH hK hL₁K).2.symm,
    (contained_six_full_action d hH hF9 hKH hK hL₁K ρ hρ eK hs).1,
    (six_seed_rank_and_ordinary_of_one_le d hH hF9 hKH hK hL₁K ρ hρ eK hs).2,
    six_chief_factors_of_one_le d hH hF9 hKH hK hL₁K ρ hρ eK hs⟩
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions

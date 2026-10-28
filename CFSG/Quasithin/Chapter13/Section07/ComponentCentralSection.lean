module
public import CFSG.Quasithin.Chapter13.Section07.ComponentTildeSource
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.CentralProjection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Lift

/-!
# Returning a marked plus component section to UH/V₁

The literal projection from UH/V₁ to UH/U₀ has kernel the image of U₀.
A component centralizing U₀ fixes that kernel. Perfectness therefore
identifies the reduced component sections and retains their canonical
actor equivalence. The final theorem uses the original conjugation model
and the literal componentStarEquiv on K/O₂(K).

Source: Aschbacher–Smith, 13.7.16(2) and13.7.18, printed pp.944–945.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.TransvectionRecognition Section08.TransvectionRecognition.Component
open Section08.TransvectionRecognition.Component.RecognitionStep
open ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]

theorem component_centralSectionModel_of_fixed_layer_central
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    {E F B W : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup F] [Module (ZMod 2) F]
    [Group B] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H) E)
    (c : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (σ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H) F)
    (s : BinaryConjugationSection D.H D.UH (PlusAction.fixedLayer D)
      (σ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (K : Subgroup D.H)
    (hK : IsComponent (D.H ⧸ pCore 2 D.H) (K.map (QuotientGroup.mk' (pCore 2 D.H))))
    (hcentral : K.map D.H.subtype ≤ centralizer (PlusAction.fixedLayer D : Set G))
    (τ : Representation (ZMod 2) B W)
    (eK : K.map (QuotientGroup.mk' (pCore 2 D.H)) ≃* B)
    (hm : HasCentralSectionModel σ (K.map (QuotientGroup.mk' (pCore 2 D.H))) τ eK) :
    HasCentralSectionModel ρ (K.map (QuotientGroup.mk' (pCore 2 D.H))) τ eK := by
  let π := QuotientGroup.mk' (pCore 2 D.H)
  let J := K.map π
  let : IsQuasisimple J := hK.2
  obtain ⟨p,hp,_,hpker⟩ := BinaryConjugationSection.exists_projection
    D.H D.H D.UH D.V₁ (PlusAction.fixedLayer D) le_rfl
    (PlusAction.point_le_fixedLayer h) π π (QuotientGroup.mk'_surjective _)
    (MonoidHom.id _) (by intro k; rfl) ρ σ c s
  have he : ∀ k : J, ∀ v, p.toLinearMap (ρ k v) = σ k (p.toLinearMap v) := by
    intro k v
    exact LinearMap.congr_fun (p.isIntertwining' k) v
  have hker : p.toLinearMap.ker ≤ fixedSpace ρ J := by
    rw [hpker]
    intro v hv k
    obtain ⟨k',hk',heq⟩ := k.property
    have hc : ⁅K.map D.H.subtype,PlusAction.fixedLayer D⁆ ≤ D.V₁ :=
      (commutator_eq_bot_iff_le_centralizer.mpr hcentral).le.trans bot_le
    have hh := c.fixed_on_imageSpace_of_commutator_le
      (K.map D.H.subtype) (PlusAction.fixedLayer D) hc k'
      (mem_map_of_mem D.H.subtype hk') v hv
    change ρ (π k') v = v at hh
    change ρ k.val v = v
    rwa [heq] at hh
  exact centralSectionModel_of_central_surjection ρ σ J p.toLinearMap hp he hker τ eK hm

/-- Return a plus-section model to the literal component quotient. -/
theorem source_hasSectionModel_of_plus_model
    {T : Sylow 2 G} {L V V₁ V₃ H : Subgroup G}
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKs : IsComponent (Section08.Source.Hstar H) (Section08.Source.starImage H K))
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H))))
    {F B W : Type*} [AddCommGroup F] [Module (ZMod 2) F]
    [Group B] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (Section08.Source.Hstar H) F)
    (s : BinaryConjugationSection H (Section08.Source.UH H V₃)
      (PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hcentral : K ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G))
    (τ : Representation (ZMod 2) B W) (eK : Section08.Source.starImage H K ≃* B)
    (hm : HasCentralSectionModel σ (Section08.Source.starImage H K) τ eK) :
    HasSectionModel H V₃ V₁ ρ K hKH τ
      ((Section08.Components.componentStarEquiv H K hKH hK).trans eK) := by
  have hc : (K.subgroupOf H).map H.subtype ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G) := by
    rwa [map_subgroupOf_eq_of_le hKH]
  exact hasSectionModel_of_star_model K hKH hK ρ hρ τ eK
    (component_centralSectionModel_of_fixed_layer_central h ρ c σ s (K.subgroupOf H)
      hKs hc τ eK hm)
end CFSG.Quasithin.Chapter13.Section07

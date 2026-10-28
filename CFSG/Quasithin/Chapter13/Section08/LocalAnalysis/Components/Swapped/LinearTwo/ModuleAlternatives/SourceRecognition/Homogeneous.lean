module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Sections
public import Theory.Representation.BinaryOffender.Homogeneous.Existence

/-!
# Homogeneous maximal source sections

In the central branch, A.1.42 selects an Irr⁺ member homogeneous under the
literal Sylow image T*. Centrality and maximality of W then make its
ambient orbit the whole source module. Since H* = K₀*T*, its T* orbit
already spans that same module. The two orbit identities are retained in
the conclusion for the F.9.18(5) refinement, with no classification input.

The FF cross-factor conclusion and the orthogonal whole-module coordinates
remain unproved here.

Source: Aschbacher–Smith, A.1.42, printed p.32; F.9.18(5–6), pp.325–326;
and 13.8.16(1), p.952.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
open F918Sections.NoStrong
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
open SolvableExclusion Three.Supercritical.Offenders
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)
include d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving


/-- The source maximal-section alternative, including the homogeneous
Irr⁺ witness and both literal full-orbit identities in the central branch. -/
theorem source_homogeneous_section_dichotomy {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [hEA : IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) :
    ∃ W : Subrepresentation ρ, W ≠ ⊤ ∧
      (∀ Y : Subrepresentation ρ, W ≤ Y → Y ≠ ⊤ → Y = W) ∧
      (sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ ≠ ⊥ ∧
      ((IsFFModule (imageRepresentation W.toRepresentation) ∧
        IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
       (subspaceCommutator ρ W.toSubmodule (Source.starImage H (conjugateSpanBy K (T : Subgroup G))) = ⊥ ∧
        ∃ I, Homogeneous.IsIrrPlusWith ρ (Source.starImage H (conjugateSpanBy K (T : Subgroup G)))
          (Source.starImage H T) I ∧ seedSpan ρ I = ⊤ ∧
          Homogeneous.orbitSpan ρ ⊤ I = ⊤ ∧
          Homogeneous.orbitSpan ρ (Source.starImage H T) I = ⊤)) := by
  obtain ⟨W,hW,hmax,hseed,halt⟩ := source_section_dichotomy
    d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ρ hρ
  refine ⟨W,hW,hmax,hseed,?_⟩
  rcases halt with hff | ⟨hc,I,hI,_⟩
  · exact Or.inl hff
  · obtain ⟨t,ht,htn⟩ := exists_moving_element K (T : Subgroup G) hmoving
    obtain ⟨F,hF,hfin,hchar,a,_,_,ha,hS⟩ := exists_source_exchangedActor
      d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ht htn
    have hTN : Source.starImage H T ≤
        normalizer (Source.starImage H (conjugateSpanBy K (T : Subgroup G)) : Set (Source.Hstar H)) := by
      let : a.orbit.Normal := a.orbit_normal
      rw [← ha,normalizer_eq_top]
      exact le_top
    have hp : IsPGroup 2 (Source.starImage H T) := by
      rw [← hS]
      exact a.sylow.isPGroup'
    obtain ⟨J,_,hJ⟩ := Homogeneous.exists_isIrrPlusWith_le_orbitSpan ρ hTN hp hI
    have hfull := Original.moved_eq_top d h hF9all hcentral hcomm hsource hH hKH hK
      hmoving hn hmodel hgen ρ hρ
    have hspan := F918Sections.orbitSpan_eq_top_of_central_maximal
      ρ _ hfull W hW hmax ((subspaceCommutator_eq_bot_iff ρ _ _).mp hc) J hJ.isIrrPlus
    have hg : Source.starImage H (conjugateSpanBy K (T : Subgroup G)) ⊔
        Source.starImage H T = ⊤ := by
      rw [← ha,← hS]
      exact a.generated
    let U : Subrepresentation ρ := Homogeneous.orbitSubrepresentation ρ hTN hJ.isIrrPlus hg
    have hJU : seedSpan ρ J ≤ U := by
      change (seedSpan ρ J).toSubmodule ≤ U.toSubmodule
      apply Submodule.span_le.mpr
      rintro _ ⟨g,v,hv,rfl⟩
      exact U.apply_mem_toSubmodule g (Homogeneous.le_orbitSpan ρ _ J hv)
    have hU : U = ⊤ := top_unique (hspan ▸ hJU)
    have hTfull : Homogeneous.orbitSpan ρ (Source.starImage H T) J = ⊤ :=
      congrArg Subrepresentation.toSubmodule hU
    have hGfull : Homogeneous.orbitSpan ρ ⊤ J = ⊤ := by
      apply top_unique
      rw [← hTfull]
      apply iSup_le
      intro t
      exact le_iSup (fun g : (⊤ : Subgroup (Source.Hstar H)) => J.map (ρ g))
        ⟨t,trivial⟩
    exact Or.inr ⟨hc,J,hJ,hspan,hGfull,hTfull⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition

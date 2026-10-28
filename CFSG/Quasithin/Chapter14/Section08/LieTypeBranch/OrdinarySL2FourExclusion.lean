module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.SL2FourExclusion
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySixFullSpan
public import CFSG.Quasithin.Chapter13.Section07.TildeOffenders
/-!
# The natural SL₂(4) exclusion at the maximal ordinary counterexample

The maximal original counterexample supplies Hypothesis12.2.1 and the earlier
F.9 application. The faithful literal action on UH/V₁ supplies the coordinates
needed by the natural-cover cubic calculation. The selected actor then allows
at most four noncentral binary chief factors, whereas duality and the actual
A₄ quotient force five. The original kernel equality, component containment
and natural marking remain the exact earlier source inputs.

Source: Aschbacher–Smith13.7.8 and13.7.21, printed pp.940,945–946.
-/
public section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Chapter13.Section07 Chapter13.Section08.SourceCompletion ChapterF.Section09.Setup
open Chapter13.Section08.TransvectionRecognition
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.TransvectionRecognition.Component
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
/-- The maximal ordinary source supplies the earlier F.9 and literal quotient coordinates to the selected natural SL₂(4) exclusion. -/
theorem original_sl2Four_selected_component_false
    [(V₁.subgroupOf (Chapter13.Section08.Source.UH G₁ V₃)).Normal]
    [IsElementaryAbelian 2 (Chapter13.Section08.Source.Utilde G₁ V₃ V₁)]
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hV : ¬ IsMulCommutative (Chapter13.Section08.Source.VH G₁ V))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hsquare : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Chapter13.Section08.Source.UH G₁ V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (G₁ ⧸ pCore 2 G₁) W)
    (s : Representation.BinaryConjugationSection G₁ (Chapter13.Section08.Source.UH G₁ V₃)
      ((Chapter13.Section08.Source.UH G₁ V₃) ⊓ centralizer (G₁.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 G₁))))
    (B : Subgroup (G₁ ⧸ pCore 2 G₁)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Chapter13.Section08.Source.VH G₁ V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf G₁).map
        (QuotientGroup.mk' (pCore 2 G₁)))
    (hKH : K ≤ G₁) (hK : (K.subgroupOf G₁).IsCComponent)
    (hKstar : IsComponent (G₁ ⧸ pCore 2 G₁) (Chapter13.Section08.Source.starImage G₁ K))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁) = G₁.pCoreIn 2)
    (hcomm : ⁅Chapter13.Section08.Source.starImage G₁ K,B⁆ = Chapter13.Section08.Source.starImage G₁ K)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Chapter13.Section08.Source.Hstar G₁)
      (Additive (Chapter13.Section08.Source.Utilde G₁ V₃ V₁)))
    (hρ : IsConjugation G₁ V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* Representation.SL2FourNatural.SL)
    (hs : HasSectionModel G₁ V₃ V₁ ρ K hKH
      (Representation.SL2OrthogonalCover.binaryNatural (F := Representation.SL2FourNatural.F)) eK)
    (hcentral : K ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁) : Set G))
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G)) : False := by
  obtain ⟨h,hU,hne⟩ := original_six_full_span_inputs_of_plane_noncentral d hmax eL hV hm
  let D := ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁
  have heq : G₁=D.Gz := d.first_normalizer.trans
    (le_antisymm (normalizer_le_centralizer_of_card_two V₁ d.line_card)
      (Subgroup.centralizer_le_normalizer _))
  have d' : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz := heq ▸ d
  have h1221 := hypothesis1221_of_maximal_natural_six d hmax eL
  have h1221' := hypothesis1221_of_maximal_natural_six d' hmax eL
  have hVGz : ¬IsMulCommutative (conjugateSpanBy D.V D.Gz) := heq ▸ hV
  have hH : G₁ ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T G₁ M := by
    have ht := OrdinarySource.point_normalizer_mem_Hz_of_nonabelian_full d' h1221' hVGz
    have ht' : G₁ ∈ Chapter13.Section08.Source.Hz D.L₁ T G₁ M := heq.symm ▸ ht
    have hl := PlusAction.source_local_residual_eq d h
    exact hl ▸ ht'
  let : IsElementaryAbelian 2 V := d.chosen.elementary
  let : IsElementaryAbelian 2 V₃ := IsElementaryAbelian.of_le d.seed_le
  let : IsMulCommutative (conjugateSpanBy V₃ G₁) := hU
  let : IsElementaryAbelian 2 (Chapter13.Section08.Source.UH G₁ V₃) :=
    conjugateSpanBy_elementary_of_commutative V₃ G₁
  let U := Chapter13.Section08.Source.UH G₁ V₃
  obtain ⟨hE,τ,c,hτ,hcoord,_,_⟩ := source_tilde_offenders d h hU hV g hsquare hout
  have heqρ : τ = ρ := by
    apply MonoidHom.ext
    intro a
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 G₁) a
    apply LinearMap.ext
    intro v
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf U) v.toMul
    have he := c.equivariant a u
    rw [hcoord,hcoord] at he
    exact he.symm.trans (hρ a u).symm
  subst τ
  exact source_sl2Four_selected_false d hH h hV hne g hsquare hout σ s B hB hBA
    hKH hK hKstar hk hcomm hL₁K ρ hρ eK hs hcentral hspan c
end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch

module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.SelectedBaumann
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySixFullSpan
public import CFSG.Quasithin.Chapter13.Section07.TildeOffenders

/-!
# The selected-component contradiction at the maximal ordinary counterexample

The maximal counterexample supplies Hypothesis12.2.1 and the original F.9
setup. Construct the faithful raw quotient action from the same conjugator
and plus offender, retain every B.5 model mark, and apply the source row
contradictions. No chosen model, point-residual containment, raw action or
normality premise remains in this maximal source consumer.

The earlier plane noncentrality, plus-kernel equality, fixed-layer
centrality and normalizer-escape-to-block inputs remain explicit for their
source producers.
Source: Aschbacher–Smith 13.7.18–21, printed pp.945–946.
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
theorem original_six_selected_false_of_block
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
    (hcentral : K ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁) : Set G))
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G))
    (hblock : (¬ G₁ ⊓ normalizer
      ((sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ M) →
      ChapterC.IsAlternatingBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) 6) : False := by
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
  let := hE
  have hτconj : IsConjugation G₁ V₃ V₁ τ := by
    intro a u
    have he := c.equivariant a u
    rw [hcoord,hcoord] at he
    exact he.symm
  have hm' : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥ := by
    rwa [←d.first_normalizer]
  exact OrdinarySource.source_selected_component_false_of_block d eL h1221 hm' hH h hV hne
    g hsquare hout σ s B hB hBA hKH hK hKstar hk hcomm τ hτconj c hcentral hspan hblock
theorem original_six_selected_false_of_baumann
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
    (hcentral : K ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁) : Set G))
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G))
    (hBnormal : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M) : False := by
  obtain ⟨h,_,_⟩ := original_six_full_span_inputs_of_plane_noncentral d hmax eL hV hm
  apply original_six_selected_false_of_block d hmax eL hV hm g hsquare hout
    σ s B hB hBA hKH hK hKstar hk hcomm hcentral hspan
  intro hes
  apply False.elim
  apply hes
  rw [PlusAction.source_local_residual_eq d h] at hBnormal
  exact inf_le_right.trans ((Stellmacher.normalizer_le_normalizer_baumann _).trans hBnormal)

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch

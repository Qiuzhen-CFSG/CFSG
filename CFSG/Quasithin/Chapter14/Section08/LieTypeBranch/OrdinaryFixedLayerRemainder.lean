module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySelectedExclusion
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.Complete
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerCatalogue

/-!
# The moving fixed-layer remainder at the maximal ordinary source

The selected-component contradiction first forces the component to move the
fixed layer.  The faithful-local source catalogue then leaves the alternating
five, projective-three, and alternating-six rows.  The completed fixed-layer
source excludes the projective-three row, leaving the two alternating rows.

The theorem keeps the genuine `Source1332OneTwo` catalogue and Baumann
normalizer hypotheses explicit; it is only an adapter for the original
maximal-counterexample packet.  Source: Aschbacher--Smith 13.7.16(2),
13.7.18--21, printed pp. 944--946.
-/

public section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Chapter13.Section07 Chapter13.Section08.SourceCompletion ChapterF.Section09.Setup
open Chapter13.Section08.TransvectionRecognition
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.TransvectionRecognition.Component
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem original_six_selected_fixedLayer_alternating
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
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G))
    (hBnormal : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T) :
    ⁅PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁),K⁆ ≠ ⊥ ∧
    (Chapter1.Section02.LocalModels.IsAlternating (Chapter13.Section08.Source.starImage G₁ K) 5 ∨
      Chapter1.Section02.LocalModels.IsAlternating (Chapter13.Section08.Source.starImage G₁ K) 6) := by
  obtain ⟨h,hU,hne⟩ := original_six_full_span_inputs_of_plane_noncentral d hmax eL hV hm
  have hnotc : ¬ K ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁) : Set G) := by
    intro hc
    exact original_six_selected_false_of_baumann d hmax eL hV hm g hsquare hout
      σ s B hB hBA hKH hK hKstar hk hcomm hc hspan hBnormal
  have hmove : ⁅PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁),K⁆ ≠ ⊥ := by
    intro he
    apply hnotc
    apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]
  refine ⟨hmove, ?_⟩
  let : IsElementaryAbelian 2 V := d.chosen.elementary
  let : IsElementaryAbelian 2 V₃ := IsElementaryAbelian.of_le d.seed_le
  let : IsMulCommutative (conjugateSpanBy V₃ G₁) := hU
  have hE : IsElementaryAbelian 2 (Chapter13.Section08.Source.UH G₁ V₃) :=
    conjugateSpanBy_elementary_of_commutative V₃ G₁
  have hmove' : ⁅PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁),
        (K.subgroupOf G₁).map G₁.subtype⁆ ≠ ⊥ := by
    rwa [map_subgroupOf_eq_of_le hKH]
  have ha := (source_plus_component_irrPlus_and_actor d h hU hV hne g hsquare hout
    σ s B hB hBA (K.subgroupOf G₁) hKstar hk hcomm).2
  rcases PlusAction.component_model_of_fixedLayer_movement h hE h1332
      (K.subgroupOf G₁) hK hmove' ha with h5 | h3 | h6
  · exact Or.inl h5
  · apply False.elim
    apply hnotc
    have hc := source_linear_three_component_centralizes_fixedLayer d h hU hV hne
      g hsquare hout σ s B hB hBA (K.subgroupOf G₁) hK hKstar hk hcomm h3
    rwa [map_subgroupOf_eq_of_le hKH] at hc
  · exact Or.inr h6

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch

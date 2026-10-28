module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.ModuleSieve.Containing
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.ModuleSieve.FixedClassification
public import Theory.Representation.BinaryPermutationSixCover.SeedConjugation

/-!
# Reduction (g) on the original selected moved module

The fixed point of the original natural flag becomes the constant word in an
augmentation-core marking. The eight-element seed is invariant under the
two-perfect point residual. The degree-six core calculation forces that
residual's two-core to fix the seed, contrary to its original natural action.
The marking uses the faithful quotient by C_K(W), not K/O₂(K).

The universal fixed-module classification is the fixed-space clause of
13.3.2(3), owned by qt-d-1332-source. The remaining module sieve and block
assembly stay with qt-d-13314-ordinary-blocks, with final source assembly in
qt-d-1378-source.
Source: Aschbacher--Smith, 13.3.2(3) and 13.3.14(g), pp.885 and 893.
-/

public section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality


open Chapter12.Section02 ChapterB.QuasisimpleSource

/-- Coordinates from the faithful quotient retain the original conjugation action. -/
theorem faithful_chosen_action_coordinates
    {G F R : Type*} [Group G] [Finite G] [Group F]
    [AddCommGroup R] [Module (ZMod 2) R]
    {T : Sylow 2 G} {B W : Subgroup G} (D : ChosenModule T B W)
    (σ : Representation (ZMod 2) F R)
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulAction σ) :
    ∃ β : B →* F, Function.Surjective β ∧
      ∃ c : W ≃* Multiplicative R, ∀ (b : B) (w : W),
        (c (W.normalizerMonoidHom ⟨b,D.normalizes b.property⟩ w)).toAdd =
          σ (β b) (c w).toAdd := by
  let := D.actionCentralizer_normal
  let β := e.groupEquiv.toMonoidHom.comp
    (QuotientGroup.mk' ((centralizer (W : Set G)).subgroupOf B))
  let c := D.spaceEquiv.symm.trans e.linearEquiv.toAddEquiv.toMultiplicative
  refine ⟨β,e.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _),c,?_⟩
  intro b w
  let v : D.space := (D.spaceEquiv.symm w).toAdd
  have he := e.intertwines (QuotientGroup.mk' ((centralizer (W : Set G)).subgroupOf B) b) v
  have hv : D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction b v)) =
      W.normalizerMonoidHom ⟨b,D.normalizes b.property⟩ w := by
    apply Subtype.ext
    rw [D.spaceEquiv_apply]
    change (b : G) * (v.val.toMul.val : G) * (b : G)⁻¹ =
      (b : G) * (w : G) * (b : G)⁻¹
    have hh : (v.val.toMul.val : G) = (w : G) :=
      (D.spaceEquiv_apply v).symm.trans
        (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply w))
    rw [hh]
  change e.linearEquiv ((D.spaceEquiv.symm _).toAdd) = _
  rw [←hv,D.spaceEquiv.symm_apply_apply]
  exact he

open Section08.SourceCompletion Section08.TransvectionRecognition.Component.ModelExtension
open Section07.ModelExclusions
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

/-- The original selected moved module cannot carry the fixed A6 core row
when the point residual is contained in its component. -/
theorem ordinary_containing_core_action_contradiction
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1332 : SupercriticalSource.Source1332OneTwo T) (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hAK : sourceOne L T P ≤ K.map H.subtype)
    (D : ChosenModule T (K.map H.subtype)
      (Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T))
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulAction (alternatingCoreRepresentation (Fin 6))) : False := by
  obtain ⟨β,hβ,c,hc'⟩ := faithful_chosen_action_coordinates D _ e
  have hp := ordinary_movedModule_contains_fixed_line_of_actor_le d eL h1332 hc K hK hqK hf hAK
  exact ordinary_point_core_moves_seed d eL
    (SixCover.core_model_twoCore_centralizes_seed _ _ _ U P hAK ordinary_point_residual_twoPerfect
      D.normalizes (point_residual_normalizes_seed d)
      (ordinary_seed_le_movedModule_of_actor_le d eL h1332 hc K hK hqK hf hAK)
      (d.line_le_plane.trans d.plane_le_seed) (hp.trans inf_le_right)
      d.seed_card d.line_card β hβ c hc')

/-- Reduction (g) follows from the earlier universal fixed-module classification.
No actor image, seed plane or coordinates are left as local callbacks. -/
theorem ordinary_reduction_g_of_fixed_module_source
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : FixedModule1332At T L) (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T) :
    ¬ sourceOne L T P ≤ K.map H.subtype := by
  intro hAK
  obtain ⟨D⟩ := ordinary_containing_moved_module_chosen d hmax eL escape h1332 hc K hK hqK hf hAK
  obtain ⟨e⟩ := fixed d.counterexample _ hf _ D
    (ordinary_movedModule_fixed_ne_bot_of_actor_le d eL h1332 hc K hK hqK hf hAK)
  exact ordinary_containing_core_action_contradiction d eL h1332 hc K hK hqK hf hAK D e


/-- The original selected component has the A5 quotient after reduction(g).
This applies the noncontainment result to the exact normalizing and generating
point actor of the block-source contract. -/
theorem ordinary_selected_five_quotient_of_fixed_module_source
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : FixedModule1332At T L) (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hgen : ⁅K,(sourceOne L T P).subgroupOf H⁆ = K) :
    (¬ sourceOne L T P ≤ K.map H.subtype) ∧
      Nonempty ((K.map H.subtype ⧸ pCore 2 (K.map H.subtype)) ≃*
        alternatingGroup (Fin 5)) := by
  have hnot := ordinary_reduction_g_of_fixed_module_source d hmax eL escape h1332 fixed
    hc K hK hqK hf
  exact ⟨hnot,ordinary_selected_five_quotient_of_noncontainment d eL h1332
    K hK hqK hf hn hgen hnot⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality

module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySixFullSpan
public import CFSG.Quasithin.Chapter13.Section07.ComponentWholeSource
/-!
# The actual maximal counterexample selects the entire plus component

The source F.9 application and abelian seed theorem provide the local
inputs at H=G₁. The completed13.7.15 producer then constructs the literal
conjugator, faithful quotient action, minimal offender and normal
component, including its small actor catalogue, Irr⁺ and whole-module
generation. Only the genuine preceding plane noncentrality and13.7.4
kernel equality remain explicit for their source producers.

Source: Aschbacher–Smith13.7.8 opening and13.7.15, printed pp.940,943–944.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.SourceCompletion Chapter13.Section07 ChapterF.Section09.Setup
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
/-- The actual maximal ordinary counterexample selects the whole plus
component with all original13.7.15 conclusions. Plane noncentrality and
faithfulness of the plus action retain their earlier source owners. -/
theorem original_six_full_span_component
    (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ pCore 2 L)≃*alternatingGroup (Fin 6))
    (hV : ¬IsMulCommutative (conjugateSpanBy V G₁))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆≠⊥)
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁)=G₁.pCoreIn 2) :
    ∃ g : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left g))^2 = 1 ∧
      V ≤ V₃ ⊔ conjugate V₁ (g : G) ∧
      ¬ conjugate V₁ (g : G) ≤ Chapter13.Section08.Source.UH G₁ V₃ ∧
      let U := Chapter13.Section08.Source.UH G₁ V₃
      let U₀ := U ⊓ centralizer (G₁.pCoreIn 2 : Set G)
      let Q := (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2
      let A := conjugate (Chapter13.Section08.Source.VH G₁ V) (g : G) ⊓ Q
      let π := QuotientGroup.mk' (pCore 2 G₁)
      ∃ hE : IsElementaryAbelian 2 U, letI := hE;
        ∃ (σ : Representation (ZMod 2) (G₁ ⧸ pCore 2 G₁) (Additive (U ⧸ U₀.subgroupOf U)))
          (s : Representation.BinaryConjugationSection G₁ U U₀ (σ.comp π))
          (B : Subgroup (G₁ ⧸ pCore 2 G₁)) (K : Subgroup G₁),
          Function.Injective σ ∧ IsMinimalBestOffender σ B ∧
          B ≤ (A.subgroupOf G₁).map π ∧
          B ≤ centralizer (fittingSubgroup (G₁ ⧸ pCore 2 G₁) : Set (G₁ ⧸ pCore 2 G₁)) ∧
          K.IsCComponent ∧ IsComponent (G₁ ⧸ pCore 2 G₁) (K.map π) ∧
          B ≤ normalizer (K.map π : Set (G₁ ⧸ pCore 2 G₁)) ∧
          ⁅K.map π,B⁆ = K.map π ∧
          Module.finrank (ZMod 2) (s.imageSpace V₃) = 2 ∧
          subspaceCommutator σ ⊤ B ≤ s.imageSpace V₃ ∧
          IsIrrPlus σ (K.map π) (subspaceCommutator σ ⊤ (K.map π)) ∧
          SmallMoved.ActorList (K.map π) ∧ K.Normal ∧
          subspaceCommutator σ ⊤ (K.map π) = ⊤ := by
  obtain ⟨h,hU,hne⟩ := original_six_full_span_inputs_of_plane_noncentral d hmax e hV hm
  exact exists_source_whole_component_irrPlus_and_actor d h hU hV hne hk
end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch

module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.ActorExclusions
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.HeadQuasisimple
/-!
# Quasisimple head in the original contained-layer branch

The original escaping setup supplies a strict overcomponent in the actual
second-vector centralizer. In the contained-layer branch its head is
quasisimple: the marked residual excludes A₅ actors, and the small chief
action excludes every nonquasisimple-head alternative. The original A₇
exclusion, vector pair, Sylow subgroup and component normality are retained.

Source: Aschbacher–Smith 10.2.1, printed p.743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
theorem source_a5_original_strict_component_quasisimple_head
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    ∃ t : G, t∈(T : Subgroup G) ∧ t∉normalizer (L : Set G) ∧
      ∃ p : SourceA5OriginalFixedPair D t,
      Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G))
        (centralizer ({p.second}:Set G)) ∧
      ∃ I : Subgroup G, L<I ∧ I≤centralizer ({p.second} : Set G) ∧
        (I.subgroupOf (centralizer ({p.second} : Set G))).IsCComponent ∧
        centralizer ({p.second} : Set G)≤normalizer (I : Set G) ∧
        ¬ Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) ∧
        ((blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype≤pCore 2 I →
          IsQuasisimple (I ⧸ pCore 2 I)) := by
  obtain ⟨t,ht,htn,p,hS,I,hLI,hIX,hI,hNI,hseven,hfive⟩ :=
    source_a5_original_strict_component_actor_exclusions D e hn hout
  refine ⟨t,ht,htn,p,hS,I,hLI,hIX,hI,hNI,hseven,?_⟩
  intro hU
  have hv := (source_conjugate_layer_cubic_centralizes_original D e hn hout t p.second ht
    p.second_layer p.second_fixed p.second_ne p.second_opposite).1
  exact source_a5_involution_overcomponent_head_quasisimple D e hn hout hv hLI.le hIX hI hS hU
    (hfive hU)
end CFSG.Quasithin.Chapter10

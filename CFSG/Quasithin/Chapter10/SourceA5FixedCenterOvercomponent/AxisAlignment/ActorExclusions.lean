module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.SourceComponent
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.ActorFiveExclusion
/-!
# Original overcomponent with both actor exclusions

The original escaping setup supplies the same fixed pair, orthogonal
coordinates, centralizer Sylow and strict overcomponent used in the cubic
A₇ exclusion. The point-residual argument additionally excludes A₅ as the
faithful actor whenever the original layer is contained in O₂(I).
All coordinates and residual premises are discharged. The contained-layer
condition remains the explicit branch of the source recognition argument.

Source: Aschbacher–Smith 10.2.1, printed p.743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
/-- The actual original strict component has no A₇ head and, in its
contained-layer branch, no A₅ faithful actor. -/
theorem source_a5_original_strict_component_actor_exclusions
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
          ¬ Nonempty ((I ⧸ centralizer
            (normalClosure ((blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype:Set I):Set I))
            ≃* alternatingGroup (Fin 5))) := by
  have hne := source_a5_fixed_center_ne_bot_of_escape D e hn hout
  obtain ⟨t,ht,htn,hgen,⟨p⟩⟩ := source_a5_exists_original_fixed_pair D e hn hout
  obtain ⟨H,hH,hHN,hWE,hred,g,hg,hresq,S,hS,hSM,hSA,hG6,hr,hclass,
    hP,hC,hM,hthree,hnot,d,hbinary,c,ew,hw,hA,hB⟩ :=
    source_exists_escaping_orthogonal_action D e hn hout
  let := hred.normal
  let := hred.elementary
  obtain ⟨c',ew',hw',u₁,u₂,a,b,ha,hb,hc₁,hc₂,hu₁,hu₂,_,_⟩ :=
    source_a5_original_pair_coordinates D e hn hne hout ht htn p hgen
      hH hWE hred S hSA hG6.faithful c ew hw
  obtain ⟨I,hLI,hIX,hI,hNI,hseven⟩ := source_a5_original_fixed_pair_strict_component_not_seven
    D e hn hout ht p hH hHN hred S c' ew' hw' u₁ u₂ a b ha hb hc₁ hc₂ hu₁ hu₂
  have hSX := (source_a5_conjugate_layer_element_component D e hn hout ht
    p.second_layer p.second_sylow p.second_ne p.second_opposite p.second_centralizer).1
  refine ⟨t,ht,htn,p,hSX,I,hLI,hIX,hI,hNI,hseven,?_⟩
  intro hU
  let W := conjugateSpanBy (omegaOneCenterAmbient (T:Subgroup G)) H
  let q := QuotientGroup.mk' (centralizer (W.subgroupOf H:Set H))
  let f := ew'.toMonoidHom.comp q
  have hf : Function.Surjective f := ew'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfix₁ := fun h:H => orthogonal_ambient_action_fixed_iff H.subtype H.subtype_injective
    (W.subgroupOf H) S c' ew' hw' h u₁
  have hfix₂ := fun h:H => orthogonal_ambient_action_fixed_iff H.subtype H.subtype_injective
    (W.subgroupOf H) S c' ew' hw' h u₂
  simp only [hc₁] at hfix₁
  simp only [hc₂] at hfix₂
  change (∀h:H,(BinaryFourPlus.wreathToIsometry (f h)).val (a,0)=(a,0) ↔
    (h:G)∈centralizer ({((u₁.val.toMul:H):G)}:Set G)) at hfix₁
  change (∀h:H,(BinaryFourPlus.wreathToIsometry (f h)).val (0,b)=(0,b) ↔
    (h:G)∈centralizer ({((u₂.val.toMul:H):G)}:Set G)) at hfix₂
  rw [hu₁] at hfix₁
  rw [hu₂] at hfix₂
  exact source_a5_fixed_center_overcomponent_actor_not_five D e hn hout hH hHN f hf
    p.first p.second a b ha hb hfix₁ hfix₂ p.first_layer p.first_fixed
    p.second_centralizer hLI.le hIX hI hNI hSX hU
end CFSG.Quasithin.Chapter10

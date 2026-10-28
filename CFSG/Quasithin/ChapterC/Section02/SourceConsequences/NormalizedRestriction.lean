module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Restriction
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.GroupTheory.SylowLocalCore
import Mathlib.Tactic
/-!
# Restricting normalized C.2.8 over the original local Sylow group

When M normalizes the original L, its conjugate span is L. An intermediate
N containing L, R and O₂(M) retains C.2.8 with local subgroup M ∩ N.
The characteristic-two condition restricts over O₂(M); the same section
Sylow restricts over R, and all module and characteristic-normalizer data
remain literal. In particular N may contain just L and the supplied Sylow
of M, as in the initial reductions of C.3 and C.4.

Source: Aschbacher–Smith C.2.9(3), C.3.1 and C.4.2, pp.147,149,152.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H M L R V N : Subgroup G}

/-- C.2.8 restriction preserving the original L, R and V. -/
theorem restrict_normalized_of_core_le (h : HypothesisC28 κ H M L R V)
    (hnorm : M ≤ normalizer (L : Set G)) (hNH : N ≤ H)
    (hLN : L ≤ N) (hRN : R ≤ N) (hcore : M.pCoreIn 2 ≤ N) :
    HypothesisC28 κ N (M ⊓ N) L R V := by
  have hs : conjugateSpanBy L M = L :=
    le_antisymm (conjugateSpanBy_le le_rfl hnorm) (le_conjugateSpanBy _ _)
  have hs' : conjugateSpanBy L (M ⊓ N) = L :=
    le_antisymm (conjugateSpanBy_le le_rfl (inf_le_left.trans hnorm)) (le_conjugateSpanBy _ _)
  let P := (M ⊓ N).subgroupOf M
  let e : P ≃* (M ⊓ N : Subgroup G) := subgroupOfEquivOfLe inf_le_left
  have hcM : centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
    rw [←h.local_fitting]
    exact centralizer_generalizedFitting_le M
  have hcP : pCore 2 M ≤ P := by
    intro x hx
    exact ⟨x.property,hcore (mem_map_of_mem M.subtype hx)⟩
  have hfP := generalizedFitting_eq_pCore_of_selfCentralizing 2
    (centralizer_pCore_le_of_pCore_le P hcM hcP)
  have hf : generalizedFitting (M ⊓ N : Subgroup G) = pCore 2 (M ⊓ N : Subgroup G) := by
    simpa only [map_generalizedFitting_equiv,pCore_map_iso] using congrArg (map e.toMonoidHom) hfP
  have hQHN : H.pCoreIn 2 ≤ N := h.ambient_core_le_radical.trans hRN
  have hQQ : H.pCoreIn 2 ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
    hQHN (hNH.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
  let f : N →* H := inclusion hNH
  have hmR : (R.subgroupOf N).map f = R.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy
    · intro hx; exact ⟨⟨x,hRN hx⟩,hx,rfl⟩
  refine
    { sqtk := ⟨h.sqtk.stronglyQuasithin.of_injective f (inclusion_injective hNH),
        h.sqtk.isKGroup.of_injective f (inclusion_injective hNH)⟩
      radical_isTwoGroup := h.radical_isTwoGroup
      radical_le := le_inf h.radical_le hRN
      local_le := inf_le_right
      local_fitting := hf
      core_nontrivial := fun he => h.core_nontrivial (bot_unique (he ▸ hQQ))
      component_le := le_inf h.component_le hLN
      component := h.component.subgroupOf_of_le (le_inf h.component_le hLN) inf_le_left
      section_sylow := ?_
      characteristic_control := ?_
      module_nontrivial := h.module_nontrivial
      module_elementary := h.module_elementary
      module_le := ?_
      module_commutator := ?_
      module_central := ?_
      module_normalizer := ?_ }
  · have hSyl := h.section_sylow
    rw [hs] at hSyl
    obtain ⟨S,hS⟩ := hSyl
    have hsmall : twoSectionCentralizer L (M ⊓ N) ≤ twoSectionCentralizer L M :=
      fun _ hx => ⟨hx.1.1,hx.2⟩
    have hRsmall : R ≤ twoSectionCentralizer L (M ⊓ N) := by
      have hRC : R ≤ twoSectionCentralizer L M := hS ▸ map_subtype_le _
      intro x hx
      exact ⟨⟨(hRC hx).1,hRN hx⟩,(hRC hx).2⟩
    obtain ⟨S',hS'⟩ := S.exists_map_subtype_eq_of_le hsmall (hS ▸ hRsmall)
    rw [hs']
    exact ⟨S',hS'.trans hS⟩
  · have hc := map_characteristicNormalizerClosure_le f (inclusion_injective hNH) (R.subgroupOf N)
    rw [hmR] at hc
    intro x hx
    exact ⟨h.characteristic_control (hc (mem_map_of_mem f hx)),x.property⟩
  · simpa only [hs',hs] using h.module_le
  · simpa only [hs',hs] using h.module_commutator
  · rw [hs']
    have hc := h.module_central
    rw [hs] at hc
    exact hc
  · intro x hx
    exact ⟨h.module_normalizer ⟨hNH hx.1,hx.2⟩,hx.1⟩

/-- The actual L·T overgroup reduction; no containment of all of M is needed. -/
theorem restrict_normalized_over_sylow (h : HypothesisC28 κ H M L R V)
    (hnorm : M ≤ normalizer (L : Set G)) (T : Sylow 2 M)
    (hRT : R ≤ (T : Subgroup M).map M.subtype)
    (hTN : (T : Subgroup M).map M.subtype ≤ N)
    (hLN : L ≤ N) (hNH : N ≤ H) : HypothesisC28 κ N (M ⊓ N) L R V := by
  apply h.restrict_normalized_of_core_le hnorm hNH hLN (hRT.trans hTN)
  exact (pCoreIn_le_sylow M T).trans hTN
end CFSG.Quasithin.ChapterC.HypothesisC28

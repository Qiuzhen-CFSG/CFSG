module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Radical
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import Theory.GroupTheory.RadicalNormalizerControl
import Mathlib.Tactic
/-!
# Restricting the genuine C.2.8 configuration

Radicality puts the ambient two-core inside R. Therefore every intermediate
overgroup of M retains a nontrivial two-core. Faithful inclusion transports
the characteristic-normalizer bound, while all original local and module
subgroups remain unchanged. This supplies the normalizer restriction used
in C.2.12 without assuming a new source configuration.

Source: Aschbacher–Smith, C.2.9(3), printed p.147, for overgroups of M.
-/
public section
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H M L R V : Subgroup G}

theorem ambient_core_le_radical (h : HypothesisC28 κ H M L R V) : H.pCoreIn 2 ≤ R := by
  have hc := pCore_le_of_pCore_normalizer_le (R.subgroupOf H) h.isRadical.isPGroup h.isRadical.2.le
  rintro x ⟨y,hy,rfl⟩
  exact hc hy

/-- The source hypothesis restricts to every actual intermediate overgroup of M.
This is the part of C.2.9(3) needed by the normalizer argument of C.2.12. -/
theorem restrict (h : HypothesisC28 κ H M L R V) {N : Subgroup G}
    (hMN : M ≤ N) (hNH : N ≤ H) : HypothesisC28 κ N M L R V := by
  let f : N →* H := inclusion hNH
  have hf : Function.Injective f := inclusion_injective hNH
  have hRN := h.radical_le.trans hMN
  have hRH := hRN.trans hNH
  have hmR : (R.subgroupOf N).map f = R.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,hRN hx⟩,hx,rfl⟩
  have hQHN : H.pCoreIn 2 ≤ N := h.ambient_core_le_radical.trans hRN
  have hQQ : H.pCoreIn 2 ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
    hQHN (hNH.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
  refine
    { sqtk := ⟨h.sqtk.stronglyQuasithin.of_injective f hf,h.sqtk.isKGroup.of_injective f hf⟩
      radical_isTwoGroup := h.radical_isTwoGroup
      radical_le := h.radical_le
      local_le := hMN
      local_fitting := h.local_fitting
      core_nontrivial := fun he => h.core_nontrivial (bot_unique (he ▸ hQQ))
      component_le := h.component_le
      component := h.component
      section_sylow := h.section_sylow
      characteristic_control := ?_
      module_nontrivial := h.module_nontrivial
      module_elementary := h.module_elementary
      module_le := h.module_le
      module_commutator := h.module_commutator
      module_central := h.module_central
      module_normalizer := (inf_le_inf_right _ hNH).trans h.module_normalizer }
  have hmap := map_characteristicNormalizerClosure_le f hf (R.subgroupOf N)
  rw [hmR] at hmap
  intro n hn
  exact h.characteristic_control (hmap (mem_map_of_mem f hn))
end CFSG.Quasithin.ChapterC.HypothesisC28
